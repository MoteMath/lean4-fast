use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;

use bytemuck::{Pod, Zeroable};

pub const STEP_FLAG_RAT: u32 = 1 << 0;
pub const STEP_FLAG_DUPLICATE_ID: u32 = 1 << 1;
pub const STEP_FLAG_ZERO_LIT: u32 = 1 << 2;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct LratHeader {
    pub num_steps: u32,
    pub max_clause_id: u32,
    pub num_cnf_clauses: u32,
    pub pad0: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct GpuLratStep {
    pub clause_id: u32,
    pub step_order: u32,
    pub hint_off: u32,
    pub hint_len: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct GpuLratVerdict {
    pub status: u32, // 0=Verified, 1=Rejected, 2=Delegate
    pub reason: u32,
    pub clause_id: u32,
    pub is_empty_clause: u32,
}

#[derive(Clone, Debug)]
pub struct CnfFormula {
    pub num_vars: u32,
    pub clauses: Vec<Vec<i32>>,
}

#[derive(Clone, Debug)]
pub enum LratRecord {
    Add {
        id: u32,
        lits: Vec<i32>,
        hints: Vec<i32>,
    },
    Delete {
        ids: Vec<u32>,
    },
}

/// Flat CSR representation shared between exact CPU `rayon` checker and GPU `lrat_verify.wgsl`.
#[derive(Clone, Debug)]
pub struct LratProblem {
    pub num_vars: u32,
    pub num_cnf_clauses: u32,
    pub max_clause_id: u32,
    pub cnf_has_empty_clause: bool,
    pub clause_lits: Vec<i32>,
    pub clause_off: Vec<u32>,
    pub clause_len: Vec<u32>,
    pub clause_birth_step: Vec<u32>,
    pub clause_deleted_at: Vec<u32>,
    pub steps: Vec<GpuLratStep>,
    pub step_flags: Vec<u32>,
    pub hints: Vec<i32>,
    pub parse_error: Option<String>,
}

fn next_tok<'a>(bytes: &'a [u8], pos: &mut usize) -> Option<&'a [u8]> {
    let n = bytes.len();
    loop {
        while *pos < n && bytes[*pos].is_ascii_whitespace() {
            *pos += 1;
        }
        if *pos >= n {
            return None;
        }
        if bytes[*pos] == b'c' && (*pos + 1 == n || bytes[*pos + 1].is_ascii_whitespace()) {
            while *pos < n && bytes[*pos] != b'\n' {
                *pos += 1;
            }
            continue;
        }
        break;
    }
    let start = *pos;
    while *pos < n && !bytes[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
    Some(&bytes[start..*pos])
}

fn parse_i32_tok(tok: &[u8]) -> Result<i32, String> {
    let s = std::str::from_utf8(tok).map_err(|_| "non-UTF8 integer token".to_string())?;
    let v: i32 = s.parse().map_err(|_| format!("invalid i32 token `{s}`"))?;
    if v == i32::MIN {
        return Err("literal i32::MIN overflow".to_string());
    }
    Ok(v)
}

fn parse_u32_tok(tok: &[u8]) -> Result<u32, String> {
    let s = std::str::from_utf8(tok).map_err(|_| "non-UTF8 u32 token".to_string())?;
    s.parse::<u32>()
        .map_err(|_| format!("invalid positive clause id `{s}`"))
}

pub fn parse_dimacs_cnf_bytes(bytes: &[u8]) -> Result<CnfFormula, String> {
    let mut pos = 0usize;
    let mut num_vars = 0u32;
    let mut expected_clauses: Option<usize> = None;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut cur: Vec<i32> = Vec::new();
    let mut saw_header = false;

    while let Some(tok) = next_tok(bytes, &mut pos) {
        if tok == b"p" {
            let fmt = next_tok(bytes, &mut pos).ok_or("unexpected EOF after `p`")?;
            if fmt != b"cnf" {
                return Err("expected `p cnf` header".to_string());
            }
            let nv = parse_u32_tok(next_tok(bytes, &mut pos).ok_or("missing num_vars")?)?;
            let nc = parse_u32_tok(next_tok(bytes, &mut pos).ok_or("missing num_clauses")?)?;
            num_vars = nv;
            expected_clauses = Some(nc as usize);
            clauses.reserve(nc as usize);
            saw_header = true;
            continue;
        }
        if tok == b"%" {
            break;
        }
        let lit = parse_i32_tok(tok)?;
        if lit == 0 {
            clauses.push(std::mem::take(&mut cur));
        } else {
            let v = lit.unsigned_abs();
            if v > num_vars {
                num_vars = v;
            }
            cur.push(lit);
        }
    }
    if !cur.is_empty() {
        return Err("unterminated DIMACS clause missing trailing 0".to_string());
    }
    if !saw_header && clauses.is_empty() {
        return Err("empty DIMACS CNF".to_string());
    }
    let _ = expected_clauses;
    Ok(CnfFormula { num_vars, clauses })
}

fn read_bin_leb128_u32(bytes: &[u8], pos: &mut usize) -> Result<u32, String> {
    let mut acc: u32 = 0;
    let mut shift: u32 = 0;
    loop {
        if *pos >= bytes.len() {
            return Err("unexpected EOF inside binary LRAT LEB128 integer".to_string());
        }
        let b = bytes[*pos];
        *pos += 1;
        if b == 0 {
            return Err("unexpected 0 byte inside binary LRAT LEB128 integer".to_string());
        }
        if shift == 28 && (b & !0x0Fu8) != 0 {
            return Err("binary LRAT LEB128 integer overflows 32-bit literal/ID".to_string());
        }
        acc |= u32::from(b & 0x7Fu8) << shift;
        if (b & 0x80u8) == 0 {
            return Ok(acc);
        }
        shift += 7;
    }
}

fn parse_bin_lit(bytes: &[u8], pos: &mut usize) -> Result<i32, String> {
    let raw = read_bin_leb128_u32(bytes, pos)?;
    let mag = raw >> 1;
    if mag == 0 || mag > i32::MAX as u32 {
        return Err(format!("binary LRAT literal out of range (encoded {raw})"));
    }
    let mag_i = mag as i32;
    Ok(if (raw & 1) != 0 { -mag_i } else { mag_i })
}

fn parse_bin_id(bytes: &[u8], pos: &mut usize) -> Result<u32, String> {
    let raw = read_bin_leb128_u32(bytes, pos)?;
    if (raw & 1) != 0 {
        return Err(format!("expected positive binary LRAT clause ID, got negative encoding {raw}"));
    }
    let id = raw >> 1;
    if id == 0 {
        return Err("binary LRAT clause ID cannot be 0".to_string());
    }
    Ok(id)
}

fn is_binary_lrat(bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    bytes[0] == b'a' || (bytes[0] == b'd' && bytes.contains(&0u8))
}

fn parse_binary_lrat_bytes(bytes: &[u8]) -> Result<Vec<LratRecord>, String> {
    let mut pos = 0usize;
    let mut recs = Vec::new();
    while pos < bytes.len() {
        let tag = bytes[pos];
        pos += 1;
        match tag {
            b'a' => {
                let id = parse_bin_id(bytes, &mut pos)?;
                let mut lits = Vec::new();
                loop {
                    if pos >= bytes.len() {
                        return Err(format!("unexpected EOF in binary LRAT `a` clause {id}"));
                    }
                    if bytes[pos] == 0 {
                        pos += 1;
                        break;
                    }
                    lits.push(parse_bin_lit(bytes, &mut pos)?);
                }
                let mut rup_hints: Vec<i32> = Vec::new();
                loop {
                    if pos >= bytes.len() {
                        return Err(format!("unexpected EOF in binary LRAT hints for clause {id}"));
                    }
                    let b = bytes[pos];
                    if b == 0 {
                        pos += 1;
                        break;
                    }
                    if (b & 1) != 0 {
                        return Err(format!(
                            "UnsupportedRatStep: binary LRAT clause {id} contains RAT hints"
                        ));
                    }
                    let hid = parse_bin_id(bytes, &mut pos)?;
                    let hid_i = i32::try_from(hid).map_err(|_| {
                        format!("binary LRAT hint ID {hid} exceeds signed 32-bit range")
                    })?;
                    rup_hints.push(hid_i);
                }
                if !lits.is_empty() && rup_hints.is_empty() {
                    return Err(format!(
                        "UnsupportedRatStep: binary LRAT clause {id} has no RUP hints (RAT/BVA step)"
                    ));
                }
                recs.push(LratRecord::Add {
                    id,
                    lits,
                    hints: rup_hints,
                });
            }
            b'd' => {
                let mut ids = Vec::new();
                loop {
                    if pos >= bytes.len() {
                        return Err("unexpected EOF in binary LRAT `d` record".to_string());
                    }
                    let b = bytes[pos];
                    if b == 0 {
                        pos += 1;
                        break;
                    }
                    if (b & 1) != 0 {
                        return Err("unexpected negative ID in binary LRAT `d` record".to_string());
                    }
                    ids.push(parse_bin_id(bytes, &mut pos)?);
                }
                recs.push(LratRecord::Delete { ids });
            }
            other => {
                return Err(format!(
                    "invalid binary LRAT record marker byte 0x{other:02x} at offset {}",
                    pos - 1
                ));
            }
        }
    }
    Ok(recs)
}

pub fn parse_lrat_bytes(bytes: &[u8]) -> Result<Vec<LratRecord>, String> {
    if is_binary_lrat(bytes) {
        return parse_binary_lrat_bytes(bytes);
    }
    let mut pos = 0usize;
    let mut recs: Vec<LratRecord> = Vec::new();

    while let Some(tok) = next_tok(bytes, &mut pos) {
        if tok == b"d" {
            let mut ids = Vec::new();
            loop {
                let t = next_tok(bytes, &mut pos).ok_or("unterminated `d` deletion line")?;
                if t == b"0" {
                    break;
                }
                let id = parse_u32_tok(t)?;
                if id == 0 {
                    return Err("clause ID cannot be 0 in deletion".to_string());
                }
                ids.push(id);
            }
            recs.push(LratRecord::Delete { ids });
            continue;
        }

        let first_id = parse_u32_tok(tok)?;
        if first_id == 0 {
            return Err("LRAT step ID cannot be 0".to_string());
        }

        let second = next_tok(bytes, &mut pos).ok_or("unexpected EOF after step ID")?;
        if second == b"d" {
            let mut ids = Vec::new();
            loop {
                let t = next_tok(bytes, &mut pos).ok_or("unterminated deletion line")?;
                if t == b"0" {
                    break;
                }
                let id = parse_u32_tok(t)?;
                if id == 0 {
                    return Err("clause ID cannot be 0 in deletion".to_string());
                }
                ids.push(id);
            }
            recs.push(LratRecord::Delete { ids });
        } else {
            let mut lits = Vec::new();
            let first_lit = parse_i32_tok(second)?;
            if first_lit != 0 {
                lits.push(first_lit);
                loop {
                    let t = next_tok(bytes, &mut pos).ok_or("unterminated clause literals")?;
                    let lit = parse_i32_tok(t)?;
                    if lit == 0 {
                        break;
                    }
                    lits.push(lit);
                }
            }
            let mut hints = Vec::new();
            loop {
                let t = next_tok(bytes, &mut pos).ok_or("unterminated LRAT hints")?;
                let h = parse_i32_tok(t)?;
                if h == 0 {
                    break;
                }
                hints.push(h);
            }
            recs.push(LratRecord::Add {
                id: first_id,
                lits,
                hints,
            });
        }
    }
    Ok(recs)
}

pub fn build_lrat_problem(cnf: CnfFormula, recs: Vec<LratRecord>) -> LratProblem {
    let num_cnf = cnf.clauses.len() as u32;
    let mut max_clause_id = num_cnf;
    let mut num_vars = cnf.num_vars;
    for r in &recs {
        if let LratRecord::Add { id, lits, .. } = r {
            if *id > max_clause_id {
                max_clause_id = *id;
            }
            for &l in lits {
                let v = l.unsigned_abs();
                if v > num_vars {
                    num_vars = v;
                }
            }
        }
    }

    let slots = (max_clause_id as usize) + 1;
    let mut clause_off = vec![0u32; slots];
    let mut clause_len = vec![0u32; slots];
    let mut clause_birth_step = vec![0xFFFF_FFFFu32; slots];
    let mut clause_deleted_at = vec![0xFFFF_FFFFu32; slots];

    let total_cnf_lits: usize = cnf.clauses.iter().map(|c| c.len()).sum();
    let total_step_lits: usize = recs
        .iter()
        .map(|r| match r {
            LratRecord::Add { lits, .. } => lits.len(),
            LratRecord::Delete { .. } => 0,
        })
        .sum();
    let mut clause_lits: Vec<i32> = Vec::with_capacity(total_cnf_lits + total_step_lits);
    let mut cnf_has_empty_clause = false;

    for (i, c) in cnf.clauses.iter().enumerate() {
        let cid = i + 1;
        if c.is_empty() {
            cnf_has_empty_clause = true;
        }
        clause_off[cid] = clause_lits.len() as u32;
        clause_len[cid] = c.len() as u32;
        clause_birth_step[cid] = 0;
        clause_lits.extend_from_slice(c);
    }

    let mut steps = Vec::new();
    let mut step_flags = Vec::new();
    let mut hints = Vec::new();
    let mut parse_error: Option<String> = None;

    let mut step_order = 1u32;
    for r in recs {
        match r {
            LratRecord::Delete { ids } => {
                for del_id in ids {
                    let idx = del_id as usize;
                    if idx < slots && clause_deleted_at[idx] == 0xFFFF_FFFF {
                        clause_deleted_at[idx] = step_order;
                    }
                }
            }
            LratRecord::Add { id, lits, hints: hs } => {
                let idx = id as usize;
                let mut flags = 0u32;
                if clause_birth_step[idx] != 0xFFFF_FFFF {
                    flags |= STEP_FLAG_DUPLICATE_ID;
                    if parse_error.is_none() {
                        parse_error = Some(format!("duplicate or CNF-colliding clause ID {id}"));
                    }
                } else {
                    clause_birth_step[idx] = step_order;
                    clause_off[idx] = clause_lits.len() as u32;
                    clause_len[idx] = lits.len() as u32;
                    clause_lits.extend_from_slice(&lits);
                }

                if hs.iter().any(|&h| h < 0) {
                    flags |= STEP_FLAG_RAT;
                }
                if lits.iter().any(|&l| l == 0) {
                    flags |= STEP_FLAG_ZERO_LIT;
                }

                let h_off = hints.len() as u32;
                let h_len = hs.len() as u32;
                hints.extend_from_slice(&hs);

                steps.push(GpuLratStep {
                    clause_id: id,
                    step_order,
                    hint_off: h_off,
                    hint_len: h_len,
                });
                step_flags.push(flags);
                step_order += 1;
            }
        }
    }

    if clause_lits.is_empty() {
        clause_lits.push(0);
    }
    if hints.is_empty() {
        hints.push(0);
    }

    LratProblem {
        num_vars,
        num_cnf_clauses: num_cnf,
        max_clause_id,
        cnf_has_empty_clause,
        clause_lits,
        clause_off,
        clause_len,
        clause_birth_step,
        clause_deleted_at,
        steps,
        step_flags,
        hints,
        parse_error,
    }
}

pub fn load_lrat_files(cnf_path: &Path, lrat_path: &Path) -> Result<LratProblem, String> {
    let mut cnf_buf = Vec::new();
    BufReader::new(
        File::open(cnf_path)
            .map_err(|e| format!("failed to open CNF {}: {e}", cnf_path.display()))?,
    )
    .read_to_end(&mut cnf_buf)
    .map_err(|e| format!("failed to read CNF {}: {e}", cnf_path.display()))?;

    let mut lrat_buf = Vec::new();
    BufReader::new(
        File::open(lrat_path)
            .map_err(|e| format!("failed to open LRAT {}: {e}", lrat_path.display()))?,
    )
    .read_to_end(&mut lrat_buf)
    .map_err(|e| format!("failed to read LRAT {}: {e}", lrat_path.display()))?;

    let cnf = parse_dimacs_cnf_bytes(&cnf_buf)?;
    let recs = parse_lrat_bytes(&lrat_buf)?;
    Ok(build_lrat_problem(cnf, recs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::{verify_lrat_cpu, LratStatus};
    use crate::trim::trim_lrat;

    fn encode_leb128_u64(out: &mut Vec<u8>, mut v: u64) {
        while v != 0 {
            let mut b = (v & 0x7F) as u8;
            v >>= 7;
            if v != 0 {
                b |= 0x80;
            }
            out.push(b);
        }
    }

    fn encode_bin_id(out: &mut Vec<u8>, id: u32) {
        encode_leb128_u64(out, (id as u64) * 2);
    }

    fn encode_bin_lit(out: &mut Vec<u8>, lit: i32) {
        let abs = lit.unsigned_abs() as u64;
        let mapped = if lit > 0 { 2 * abs } else { 2 * abs + 1 };
        encode_leb128_u64(out, mapped);
    }

    #[test]
    fn binary_lrat_multibyte_leb128_roundtrip_and_trim() {
        let cnf_txt = b"p cnf 70 4\n1 70 0\n-1 70 0\n1 -70 0\n-1 -70 0\n";
        let cnf = parse_dimacs_cnf_bytes(cnf_txt).unwrap();

        let mut bin = Vec::new();
        // Step 130 (multi-byte LEB128): unit 70 from hints 1, 2
        bin.push(b'a');
        encode_bin_id(&mut bin, 130);
        encode_bin_lit(&mut bin, 70);
        bin.push(0);
        encode_bin_id(&mut bin, 1);
        encode_bin_id(&mut bin, 2);
        bin.push(0);

        // Step 131: dead clause -1 from hints 2, 4
        bin.push(b'a');
        encode_bin_id(&mut bin, 131);
        encode_bin_lit(&mut bin, -1);
        bin.push(0);
        encode_bin_id(&mut bin, 2);
        encode_bin_id(&mut bin, 4);
        bin.push(0);

        // Delete 1, 2 after step 130/131
        bin.push(b'd');
        encode_bin_id(&mut bin, 1);
        encode_bin_id(&mut bin, 2);
        bin.push(0);

        // Step 132: empty clause from hints 130, 3, 4
        bin.push(b'a');
        encode_bin_id(&mut bin, 132);
        bin.push(0);
        encode_bin_id(&mut bin, 130);
        encode_bin_id(&mut bin, 3);
        encode_bin_id(&mut bin, 4);
        bin.push(0);

        let recs = parse_lrat_bytes(&bin).unwrap();
        assert_eq!(recs.len(), 4);
        let prob = build_lrat_problem(cnf.clone(), recs.clone());
        let st = verify_lrat_cpu(&prob, Some(2));
        assert!(matches!(st, LratStatus::Accepted { has_empty_clause: true, .. }), "{st:?}");

        let trimmed = trim_lrat(&cnf, &recs).unwrap();
        assert_eq!(trimmed.stats.original_adds, 3);
        assert_eq!(trimmed.stats.kept_adds, 2);
        assert_eq!(trimmed.stats.empty_clause_id, 132);
    }

    #[test]
    fn binary_lrat_explicit_unsupported_rat_step_errors() {
        let mut rat_bin = Vec::new();
        rat_bin.push(b'a');
        encode_bin_id(&mut rat_bin, 5);
        encode_bin_lit(&mut rat_bin, 1);
        rat_bin.push(0);
        encode_bin_id(&mut rat_bin, 1);
        encode_bin_lit(&mut rat_bin, -2); // negative pivot resolution hint => RAT step
        encode_bin_id(&mut rat_bin, 3);
        rat_bin.push(0);
        let err_rat = parse_lrat_bytes(&rat_bin).unwrap_err();
        assert!(err_rat.contains("UnsupportedRatStep"), "{err_rat}");

        let mut bva_bin = Vec::new();
        bva_bin.push(b'a');
        encode_bin_id(&mut bva_bin, 5);
        encode_bin_lit(&mut bva_bin, 1);
        bva_bin.push(0);
        bva_bin.push(0); // non-empty clause with empty RUP hints => BVA/RAT
        let err_bva = parse_lrat_bytes(&bva_bin).unwrap_err();
        assert!(err_bva.contains("UnsupportedRatStep"), "{err_bva}");
    }
}
