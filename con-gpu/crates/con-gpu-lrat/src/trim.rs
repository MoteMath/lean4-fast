//! Backward-reachability LRAT proof trimmer emitting Lean ASCII `LratCert` records.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use crate::parser::{CnfFormula, LratRecord};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TrimStats {
    pub original_adds: usize,
    pub original_deletes: usize,
    pub kept_adds: usize,
    pub emitted_deletes: usize,
    pub empty_clause_id: u32,
}

#[derive(Clone, Debug)]
pub struct TrimmedLrat {
    pub records: Vec<LratRecord>,
    pub ascii: String,
    pub stats: TrimStats,
}

/// Format trimmed LRAT records using Lean `Std.Tactic.BVDecide.LRAT.Parser.lratProofToString`
/// text syntax so `Std.Tactic.BVDecide.LRAT.Parser.Text.parseActions` and `con-gpu` parse it
/// identically.
pub fn format_lean_ascii_lrat(records: &[LratRecord]) -> String {
    let mut out = String::with_capacity(records.len() * 24);
    for rec in records {
        match rec {
            LratRecord::Add { id, lits, hints } => {
                let _ = write!(out, "{id} ");
                for &lit in lits {
                    let _ = write!(out, "{lit} ");
                }
                out.push_str("0 ");
                for &h in hints {
                    let _ = write!(out, "{h} ");
                }
                out.push_str("0\n");
            }
            LratRecord::Delete { ids } => {
                if ids.is_empty() {
                    continue;
                }
                out.push_str("1 d ");
                for &id in ids {
                    let _ = write!(out, "{id} ");
                }
                out.push_str("0\n");
            }
        }
    }
    out
}

/// Backward-reachability trimmer starting from the derived empty clause, computing exact causal
/// `d ... 0` deletions after the last kept use of every clause ID.
pub fn trim_lrat_records(num_cnf_clauses: usize, records: &[LratRecord]) -> Result<TrimmedLrat, String> {
    let num_cnf = u32::try_from(num_cnf_clauses)
        .map_err(|_| "CNF clause count exceeds u32::MAX".to_string())?;

    let mut original_adds = 0usize;
    let mut original_deletes = 0usize;
    let mut add_pos_by_id: HashMap<u32, usize> = HashMap::new();
    let mut empty_step: Option<(usize, u32)> = None;

    for (pos, rec) in records.iter().enumerate() {
        match rec {
            LratRecord::Delete { .. } => {
                original_deletes += 1;
            }
            LratRecord::Add { id, lits, .. } => {
                original_adds += 1;
                if *id == 0 {
                    return Err("LRAT derived clause ID cannot be 0".to_string());
                }
                if *id <= num_cnf {
                    return Err(format!(
                        "LRAT derived clause ID {id} collides with CNF clause 1..={num_cnf}"
                    ));
                }
                if add_pos_by_id.insert(*id, pos).is_some() {
                    return Err(format!("duplicate derived clause ID {id} in LRAT proof"));
                }
                if empty_step.is_none() && lits.is_empty() {
                    empty_step = Some((pos, *id));
                }
            }
        }
    }

    let (empty_pos, empty_clause_id) = empty_step
        .ok_or_else(|| "LRAT proof does not derive the empty clause".to_string())?;

    let mut needed_ids: HashSet<u32> = HashSet::new();
    let mut expanded_ids: HashSet<u32> = HashSet::new();
    let mut keep_positions: BTreeSet<usize> = BTreeSet::new();
    let mut worklist: Vec<u32> = vec![empty_clause_id];
    needed_ids.insert(empty_clause_id);
    let _ = empty_pos;

    while let Some(cid) = worklist.pop() {
        if cid == 0 {
            return Err("invalid clause ID 0 reached during LRAT trimming".to_string());
        }
        if cid <= num_cnf || !expanded_ids.insert(cid) {
            continue;
        }
        let &pos = add_pos_by_id
            .get(&cid)
            .ok_or_else(|| format!("undefined hint clause ID {cid} referenced during trimming"))?;
        keep_positions.insert(pos);

        let hints = match &records[pos] {
            LratRecord::Add { hints, .. } => hints,
            LratRecord::Delete { .. } => unreachable!(),
        };
        if hints.is_empty() {
            return Err(format!("derived clause {cid} has empty hint list"));
        }
        for &h in hints {
            if h == 0 || h == i32::MIN {
                return Err(format!("invalid hint {h} in clause {cid}"));
            }
            let hid = h.unsigned_abs();
            if hid == cid {
                return Err(format!("self-referential hint {hid} in clause {cid}"));
            }
            if hid > num_cnf {
                let &hint_pos = add_pos_by_id.get(&hid).ok_or_else(|| {
                    format!("undefined hint clause ID {hid} referenced by clause {cid}")
                })?;
                if hint_pos >= pos {
                    return Err(format!(
                        "non-causal hint {hid} used before its derivation in clause {cid}"
                    ));
                }
            }
            if needed_ids.insert(hid) {
                worklist.push(hid);
            }
        }
    }

    let mut last_use_pos: HashMap<u32, usize> = HashMap::new();
    for &pos in &keep_positions {
        if let LratRecord::Add { hints, .. } = &records[pos] {
            for &h in hints {
                last_use_pos.insert(h.unsigned_abs(), pos);
            }
        }
    }

    let mut deletes_after_pos: HashMap<usize, Vec<u32>> = HashMap::new();
    for (hid, pos) in last_use_pos {
        if hid != empty_clause_id {
            deletes_after_pos.entry(pos).or_default().push(hid);
        }
    }
    for ids in deletes_after_pos.values_mut() {
        ids.sort_unstable();
        ids.dedup();
    }

    let mut unused_cnf: Vec<u32> = (1..=num_cnf)
        .filter(|cid| !needed_ids.contains(cid))
        .collect();
    let mut trimmed = Vec::with_capacity(keep_positions.len() * 2 + 1);
    let mut emitted_deletes = 0usize;

    if !unused_cnf.is_empty() {
        unused_cnf.sort_unstable();
        emitted_deletes += unused_cnf.len();
        trimmed.push(LratRecord::Delete { ids: unused_cnf });
    }

    for &pos in &keep_positions {
        trimmed.push(records[pos].clone());
        if let Some(dels) = deletes_after_pos.remove(&pos) {
            if !dels.is_empty() {
                emitted_deletes += dels.len();
                trimmed.push(LratRecord::Delete { ids: dels });
            }
        }
    }

    let ascii = format_lean_ascii_lrat(&trimmed);
    let stats = TrimStats {
        original_adds,
        original_deletes,
        kept_adds: keep_positions.len(),
        emitted_deletes,
        empty_clause_id,
    };
    Ok(TrimmedLrat {
        records: trimmed,
        ascii,
        stats,
    })
}

pub fn trim_lrat(cnf: &CnfFormula, records: &[LratRecord]) -> Result<TrimmedLrat, String> {
    trim_lrat_records(cnf.clauses.len(), records)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::{verify_lrat_cpu, LratStatus};
    use crate::parser::{build_lrat_problem, parse_dimacs_cnf_bytes, parse_lrat_bytes};

    #[test]
    fn trim_prunes_dead_steps_and_emits_last_use_deletes() {
        let cnf_txt = b"p cnf 3 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
        let lrat_txt = b"\
5 2 0 1 2 0
6 3 0 1 3 0
7 -2 0 3 4 0
8 0 5 7 0
";
        let cnf = parse_dimacs_cnf_bytes(cnf_txt).unwrap();
        let recs = parse_lrat_bytes(lrat_txt).unwrap();
        let trimmed = trim_lrat(&cnf, &recs).unwrap();

        // Step 6 (dead clause) and literal-var-3 dead clause should be pruned cleanly.
        assert_eq!(trimmed.stats.original_adds, 4);
        assert_eq!(trimmed.stats.kept_adds, 3);
        assert_eq!(trimmed.stats.empty_clause_id, 8);
        // Should emit Lean ASCII `1 d ... 0` deletes and no comment lines.
        assert!(trimmed.ascii.contains("1 d "), "got:\n{}", trimmed.ascii);
        for line in trimmed.ascii.lines() {
            let first = line.split_whitespace().next().unwrap();
            assert!(first.parse::<u32>().is_ok(), "line `{line}` missing leading ID");
        }

        // Roundtrip through parser -> exact CPU checker must still accept!
        let reparsed = parse_lrat_bytes(trimmed.ascii.as_bytes()).unwrap();
        let prob = build_lrat_problem(cnf, reparsed);
        let status = verify_lrat_cpu(&prob, Some(2));
        assert!(matches!(status, LratStatus::Accepted { has_empty_clause: true, .. }), "status={status:?}");
    }

    #[test]
    fn trim_rejects_missing_empty_clause() {
        let cnf = parse_dimacs_cnf_bytes(b"p cnf 1 2\n1 0\n-1 0\n").unwrap();
        let recs = vec![LratRecord::Add {
            id: 3,
            lits: vec![1],
            hints: vec![1],
        }];
        let err = trim_lrat(&cnf, &recs).unwrap_err();
        assert!(err.contains("empty clause"), "{err}");
    }
}
