use std::time::Instant;

use rayon::prelude::*;

use crate::parser::{
    LratProblem, STEP_FLAG_DUPLICATE_ID, STEP_FLAG_RAT, STEP_FLAG_ZERO_LIT,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LratStatus {
    Accepted {
        total_steps: usize,
        gpu_verified_steps: usize,
        delegated_steps: usize,
        has_empty_clause: bool,
        thread_count: usize,
        elapsed_ns: u128,
        gpu_kernel_ns: u128,
        pcie_upload_ns: u128,
    },
    Rejected {
        step_idx: usize,
        clause_id: u32,
        reason: String,
        rejected_count: usize,
    },
}

pub struct StampTable {
    // 0 = unset, gen = positive var true, gen+1 = negative var true.
    marks: Vec<u32>,
    stamp: u32,
}

impl StampTable {
    fn new(num_vars: u32) -> Self {
        Self {
            marks: vec![0u32; (num_vars as usize) + 1],
            stamp: 2,
        }
    }

    fn reset(&mut self) {
        if self.stamp >= u32::MAX - 4 {
            self.marks.fill(0);
            self.stamp = 2;
        } else {
            self.stamp += 2;
        }
    }

    fn ensure_var(&mut self, v: usize) {
        if v >= self.marks.len() {
            self.marks.resize(v + 1, 0);
        }
    }

    /// Returns 1 if lit is TRUE, -1 if lit is FALSE, 0 if unassigned.
    #[inline]
    fn probe(&self, lit: i32) -> i32 {
        let v = lit.unsigned_abs() as usize;
        if v >= self.marks.len() {
            return 0;
        }
        let m = self.marks[v];
        if m == self.stamp {
            if lit > 0 { 1 } else { -1 }
        } else if m == self.stamp + 1 {
            if lit < 0 { 1 } else { -1 }
        } else {
            0
        }
    }

    /// Assigns `lit = TRUE`. Returns `false` if `-lit` was already TRUE (contradiction).
    #[inline]
    fn assign_true(&mut self, lit: i32) -> bool {
        let v = lit.unsigned_abs() as usize;
        self.ensure_var(v);
        let target = if lit > 0 { self.stamp } else { self.stamp + 1 };
        let opp = if lit > 0 { self.stamp + 1 } else { self.stamp };
        let cur = self.marks[v];
        if cur == opp {
            return false;
        }
        self.marks[v] = target;
        true
    }
}

fn check_hint_causal(prob: &LratProblem, cid: u32, step_order: u32, hid: u32) -> Result<(), String> {
    if hid == 0 || hid > prob.max_clause_id {
        return Err(format!("undefined hint clause ID {hid}"));
    }
    if hid >= cid {
        return Err(format!("non-causal hint {hid} >= derived clause {cid}"));
    }
    let idx = hid as usize;
    if prob.clause_birth_step[idx] >= step_order {
        return Err(format!("hint clause {hid} not yet derived before clause {cid}"));
    }
    if step_order >= prob.clause_deleted_at[idx] {
        return Err(format!("deleted hint clause {hid} used at step clause {cid}"));
    }
    Ok(())
}

fn verify_rup_hints(
    prob: &LratProblem,
    tbl: &mut StampTable,
    cid: u32,
    step_order: u32,
    hs: &[i32],
) -> Result<(), String> {
    if hs.is_empty() {
        return Err(format!("clause {cid} has empty hint list"));
    }
    let mut conflict = false;
    for &h_raw in hs {
        if h_raw <= 0 {
            return Err(format!("unexpected non-positive hint {h_raw} in RUP chain for {cid}"));
        }
        let hid = h_raw as u32;
        check_hint_causal(prob, cid, step_order, hid)?;
        if !conflict {
            let off = prob.clause_off[hid as usize] as usize;
            let len = prob.clause_len[hid as usize] as usize;
            let lits = &prob.clause_lits[off..off + len];
            let mut unassigned = 0i32;
            let mut unassigned_cnt = 0u32;
            for &lit in lits {
                if lit == 0 {
                    return Err(format!("zero literal in clause {hid}"));
                }
                let p = tbl.probe(lit);
                if p == 1 {
                    return Err(format!("hint clause {hid} already satisfied at clause {cid}"));
                }
                if p == 0 {
                    if unassigned_cnt == 0 {
                        unassigned = lit;
                        unassigned_cnt = 1;
                    } else if lit != unassigned {
                        return Err(format!("hint clause {hid} not unit at clause {cid}"));
                    }
                }
            }
            if unassigned_cnt == 1 {
                tbl.assign_true(unassigned);
            } else {
                conflict = true;
            }
        }
    }
    if !conflict {
        return Err(format!("no conflict reached for derived clause {cid}"));
    }
    Ok(())
}

/// Exact RUP + RAT verification of single step `step_idx`. Returns `(is_empty_clause, Ok/Err)`.
pub fn verify_step_exact(
    prob: &LratProblem,
    tbl: &mut StampTable,
    step_idx: usize,
) -> Result<bool, String> {
    let step = &prob.steps[step_idx];
    let flags = prob.step_flags[step_idx];
    let cid = step.clause_id;

    if cid == 0 || cid > prob.max_clause_id {
        return Err(format!("invalid derived clause ID {cid}"));
    }
    if (flags & STEP_FLAG_DUPLICATE_ID) != 0 {
        return Err(format!("duplicate or colliding clause ID {cid}"));
    }
    if (flags & STEP_FLAG_ZERO_LIT) != 0 {
        return Err(format!("derived clause {cid} contains zero literal"));
    }

    let c_off = prob.clause_off[cid as usize] as usize;
    let c_len = prob.clause_len[cid as usize] as usize;
    let c_lits = &prob.clause_lits[c_off..c_off + c_len];
    let h_off = step.hint_off as usize;
    let h_len = step.hint_len as usize;
    let hs = &prob.hints[h_off..h_off + h_len];

    tbl.reset();
    let mut tautology = false;
    for &lit in c_lits {
        if !tbl.assign_true(-lit) {
            tautology = true;
        }
    }
    let _ = tautology;

    if (flags & STEP_FLAG_RAT) == 0 {
        verify_rup_hints(prob, tbl, cid, step.step_order, hs)?;
    } else {
        // Exact LRAT RAT handling: pre-RUP hints before first negative ID, then one sub-branch per -rat_id.
        if c_lits.is_empty() {
            return Err(format!("empty clause {cid} cannot use RAT negative hints"));
        }
        let pivot = c_lits[0];
        let mut cursor = 0usize;
        while cursor < hs.len() && hs[cursor] > 0 {
            let hid = hs[cursor] as u32;
            check_hint_causal(prob, cid, step.step_order, hid)?;
            let off = prob.clause_off[hid as usize] as usize;
            let len = prob.clause_len[hid as usize] as usize;
            let lits = &prob.clause_lits[off..off + len];
            let mut unassigned = 0i32;
            let mut cnt = 0u32;
            for &lit in lits {
                let p = tbl.probe(lit);
                if p == 1 {
                    return Err(format!("RAT pre-hint {hid} satisfied at {cid}"));
                }
                if p == 0 {
                    if cnt == 0 {
                        unassigned = lit;
                        cnt = 1;
                    } else if lit != unassigned {
                        return Err(format!("RAT pre-hint {hid} non-unit at {cid}"));
                    }
                }
            }
            if cnt == 1 {
                tbl.assign_true(unassigned);
            } else {
                // Early RUP conflict already proves clause.
                for &rem in &hs[cursor + 1..] {
                    if rem > 0 {
                        check_hint_causal(prob, cid, step.step_order, rem as u32)?;
                    }
                }
                return Ok(c_len == 0);
            }
            cursor += 1;
        }

        let base_marks = tbl.marks.clone();
        let base_stamp = tbl.stamp;
        while cursor < hs.len() {
            let neg = hs[cursor];
            if neg >= 0 {
                return Err(format!("expected negative RAT hint at clause {cid}"));
            }
            let rat_cid = (-neg) as u32;
            check_hint_causal(prob, cid, step.step_order, rat_cid)?;
            cursor += 1;
            let sub_start = cursor;
            while cursor < hs.len() && hs[cursor] > 0 {
                cursor += 1;
            }
            let sub_hints = &hs[sub_start..cursor];

            tbl.marks = base_marks.clone();
            tbl.stamp = base_stamp;
            let roff = prob.clause_off[rat_cid as usize] as usize;
            let rlen = prob.clause_len[rat_cid as usize] as usize;
            let rlits = &prob.clause_lits[roff..roff + rlen];
            let mut blocked = false;
            for &lit in rlits {
                if lit == -pivot {
                    continue;
                }
                if !tbl.assign_true(-lit) {
                    blocked = true;
                    break;
                }
            }
            if !blocked {
                verify_rup_hints(prob, tbl, cid, step.step_order, sub_hints)?;
            } else {
                for &rem in sub_hints {
                    check_hint_causal(prob, cid, step.step_order, rem as u32)?;
                }
            }
        }
    }

    Ok(c_len == 0)
}

pub fn verify_lrat_steps_cpu(
    prob: &LratProblem,
    step_indices: &[usize],
    threads: Option<usize>,
) -> Result<(bool, usize, u128), (usize, u32, String)> {
    if let Some(err) = &prob.parse_error {
        return Err((0, 0, err.clone()));
    }
    let t0 = Instant::now();
    let nthreads = threads
        .or_else(|| {
            std::env::var("RAYON_NUM_THREADS")
                .ok()
                .and_then(|s| s.parse::<usize>().ok())
        })
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|p| p.get())
                .unwrap_or(1)
        })
        .max(1);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(nthreads)
        .build()
        .map_err(|e| (0usize, 0u32, format!("rayon thread pool error: {e}")))?;

    let results: Vec<Result<bool, (usize, u32, String)>> = pool.install(|| {
        step_indices
            .par_iter()
            .map_init(
                || StampTable::new(prob.num_vars),
                |tbl, &step_idx| {
                    verify_step_exact(prob, tbl, step_idx)
                        .map_err(|msg| (step_idx, prob.steps[step_idx].clause_id, msg))
                },
            )
            .collect()
    });

    let mut has_empty = prob.cnf_has_empty_clause;
    let mut first_err: Option<(usize, u32, String)> = None;
    for r in results {
        match r {
            Ok(is_empty) => {
                if is_empty {
                    has_empty = true;
                }
            }
            Err(e) => {
                if first_err
                    .as_ref()
                    .map(|cur| e.0 < cur.0)
                    .unwrap_or(true)
                {
                    first_err = Some(e);
                }
            }
        }
    }

    if let Some(e) = first_err {
        return Err(e);
    }
    Ok((has_empty, nthreads, t0.elapsed().as_nanos()))
}

/// Exact full CPU verification (`--backend cpu`).
pub fn verify_lrat_cpu(prob: &LratProblem, threads: Option<usize>) -> LratStatus {
    let t0 = Instant::now();
    if let Some(err) = &prob.parse_error {
        return LratStatus::Rejected {
            step_idx: 0,
            clause_id: 0,
            reason: err.clone(),
            rejected_count: 1,
        };
    }
    let all_indices: Vec<usize> = (0..prob.steps.len()).collect();
    match verify_lrat_steps_cpu(prob, &all_indices, threads) {
        Err((step_idx, clause_id, reason)) => LratStatus::Rejected {
            step_idx,
            clause_id,
            reason,
            rejected_count: 1,
        },
        Ok((has_empty, thread_count, _)) => {
            if !has_empty {
                return LratStatus::Rejected {
                    step_idx: prob.steps.len(),
                    clause_id: 0,
                    reason: "LRAT proof contains no derived empty clause".to_string(),
                    rejected_count: 1,
                };
            }
            LratStatus::Accepted {
                total_steps: prob.steps.len(),
                gpu_verified_steps: 0,
                delegated_steps: 0,
                has_empty_clause: true,
                thread_count,
                elapsed_ns: t0.elapsed().as_nanos(),
                gpu_kernel_ns: 0,
                pcie_upload_ns: 0,
            }
        }
    }
}
