//! CPU-only forensic replay of one theorem job in a fully loaded declaration stream.
//! Usage: replay_theorem INDEX EXPECTED_NAME EXPECTED_DECL_COUNT ROOT [LOAD_DIR ...]
//! Set REPLAY_TRUST_BV_DECIDE=1 to reproduce that verifier option.
use std::collections::{BTreeSet, HashSet};
use std::path::PathBuf;

use con_gpu_arena::fs::hash128_bytes;
use con_gpu_arena::loader::{build_olean_input, nidx_to_string};
use con_gpu_arena::soa_pack::{
    mix_hash32, EMPTY_NIDX_SENTINEL, JOB_FLAG_TY_GUARD_OK, JOB_FLAG_VAL_GUARD_OK,
};
use con_gpu_arena::{
    load_environment, pack_arena, verify_delegated_exact_with, ArenaLimitsConfig, GpuArenaPacket,
    LoadedEnvironment, VerifyOptions,
};
use con_ron_core::arena::env::IDeclaration;
use con_ron_core::arena::handle::{EIdx, NIdx};
use con_ron_core::arena::store::{ENodeView, EStore};

fn const_names(env: &LoadedEnvironment, root: u32) -> Result<BTreeSet<u32>, String> {
    let store = EStore::empty_frozen();
    let mut visited = HashSet::new();
    let mut names = BTreeSet::new();
    let mut stack = vec![EIdx::of_word(root)];
    while let Some(expr) = stack.pop() {
        if !visited.insert(expr.word) {
            continue;
        }
        match store
            .view(&env.pers, &expr)
            .ok_or_else(|| format!("dangling expression {}", expr.word))?
        {
            ENodeView::Const(name, _) => {
                names.insert(name.word);
            }
            ENodeView::FVar(_, ty) | ENodeView::Proj(_, _, ty) => stack.push(ty),
            ENodeView::App(a, b) | ENodeView::Lam(a, b) | ENodeView::ForallE(a, b) => {
                stack.extend([a, b])
            }
            ENodeView::LetE(a, b, c) => stack.extend([a, b, c]),
            ENodeView::BVar(_) | ENodeView::Sort(_) | ENodeView::Lit(_) => {}
        }
    }
    Ok(names)
}

// The WGSL find_const_slot_raw probes packed (name, slot+1) cells. Report that
// result separately from the exact checker's index of the same interned name.
fn packed_slot(packet: &GpuArenaPacket, name: u32) -> Option<u32> {
    let mask = packet.header.const_hash_mask;
    let mut idx = mix_hash32(name) & mask;
    for _ in 0..=mask {
        let cell = packet.header.off_const_hash as usize + idx as usize * 2;
        match packet.env_tables[cell] {
            EMPTY_NIDX_SENTINEL => return None,
            n if n == name => return packet.env_tables[cell + 1].checked_sub(1),
            _ => idx = (idx + 1) & mask,
        }
    }
    None
}

fn run() -> Result<u8, String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() < 4 {
        return Err(
            "usage: replay_theorem INDEX EXPECTED_NAME EXPECTED_DECL_COUNT ROOT [LOAD_DIR ...]"
                .into(),
        );
    }
    let index: usize = args[0].parse().map_err(|_| "invalid INDEX")?;
    let expected_count: usize = args[2].parse().map_err(|_| "invalid EXPECTED_DECL_COUNT")?;
    let paths = args[4..].iter().map(PathBuf::from).collect::<Vec<_>>();
    let spec = build_olean_input(&args[3..4], &paths, None, true);
    let opts = VerifyOptions {
        trust_bv_decide_axioms: std::env::var("REPLAY_TRUST_BV_DECIDE").as_deref() == Ok("1"),
    };
    println!("input={spec:?}\noptions={opts:?}\nprocess=cpu-only");
    let env = load_environment(&spec).map_err(|e| format!("load failed: {e:?}"))?;
    let actual_name = env.decl_name_str(index);
    println!(
        "total_decls={} decl_index={index} decl_name={actual_name}",
        env.decls.len()
    );
    let mut hashes: Vec<_> = env.module_hashes.iter().collect();
    hashes.sort_by_key(|(name, _)| *name);
    let mut digest_input = Vec::new();
    for (name, hash) in hashes {
        digest_input.extend_from_slice(&(name.len() as u64).to_le_bytes());
        digest_input.extend_from_slice(name.as_bytes());
        digest_input.extend_from_slice(hash);
    }
    println!(
        "module_count={} module_set_hash128={:02x?}",
        env.module_hashes.len(),
        hash128_bytes(&digest_input)
    );
    if env.decls.len() != expected_count || index >= env.decls.len() || actual_name != args[1] {
        return Err("input identity check failed; no declaration was replayed".into());
    }
    let IDeclaration::ThmDecl(cv, proof) = &env.decls[index] else {
        return Err("target is not a theorem declaration".into());
    };
    let ty = cv.ty.word;
    let val = proof.word;
    let cutoff = env.pers.env.firsts[index];
    let mut prefix = Vec::new();
    for i in 0..index {
        let name = env.decl_name_str(i);
        prefix.extend_from_slice(&(name.len() as u64).to_le_bytes());
        prefix.extend_from_slice(name.as_bytes());
    }
    println!(
        "prefix_first_names_hash128={:02x?} prefix_decl_count={index} host_const_cutoff={cutoff}",
        hash128_bytes(&prefix)
    );
    drop(prefix);
    let (result, telemetry) = verify_delegated_exact_with(&env, &[index], Some(1), opts);
    let exit = match result {
        Ok(()) => {
            println!("exact_host=Accepted");
            0
        }
        Err(verdict) => {
            println!("exact_host={verdict:?}");
            verdict.exit_code()
        }
    };
    println!(
        "exact_host_jobs={} exact_host_exit={exit}",
        telemetry.checked_count
    );
    let packet = pack_arena(&env, ArenaLimitsConfig::default());
    let job = packet
        .jobs
        .iter()
        .find(|j| j.orig_decl_idx as usize == index)
        .ok_or("target job missing from pack")?;
    if job.base_below as u64 != cutoff || job.ty != ty || job.val != val {
        return Err("packed target disagrees with materialized host target".into());
    }
    println!(
        "packed_target={job:?} type_guard_ok={} value_guard_ok={}",
        job.flags & JOB_FLAG_TY_GUARD_OK != 0,
        job.flags & JOB_FLAG_VAL_GUARD_OK != 0
    );
    for (side, root) in [("type", ty), ("value", val)] {
        for word in const_names(&env, root)? {
            let n = NIdx::of_word(word);
            let name = nidx_to_string(&env.pers, &n);
            let host = env.pers.env.idx.get(&n).copied();
            let gpu = packed_slot(&packet, word);
            println!("ref {side} name={name:?} word={word} host_slot={host:?} host_visible={} packed_slot={gpu:?} packed_visible={}", host.is_some_and(|i| i < cutoff), gpu.is_some_and(|i| i < job.base_below));
        }
    }
    Ok(exit)
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(code) => std::process::ExitCode::from(code),
        Err(message) => {
            eprintln!("{message}");
            std::process::ExitCode::from(3)
        }
    }
}
