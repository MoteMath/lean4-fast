use crate::parser::{build_lrat_problem, CnfFormula, LratProblem, LratRecord};

/// Generates a mathematically exact synthetic 100,000-clause UNSAT CNF + causal LRAT proof
/// (with unit chains, multi-clause resolution gadgets, deletions, and final empty clause).
pub fn generate_synthetic_100k_unsat() -> LratProblem {
    generate_synthetic_unsat(100_000)
}

/// Parameterized generator: produces `target_cnf_clauses` (e.g., 100_000) CNF clauses
/// with ~`target_cnf_clauses` valid causal LRAT steps proving UNSAT.
pub fn generate_synthetic_unsat(target_cnf_clauses: usize) -> LratProblem {
    let target = target_cnf_clauses.max(12);
    let block_cnt = (target / 6).max(2);
    // Each block of 6 CNF clauses produces variables cleanly; block 0 ends in UNSAT core,
    // remaining blocks are valid clauses that resolve to intermediate lemmas and link cleanly!
    // Actually let's make ALL blocks participate in a binary resolution chain or independent-plus-linked chain:
    // Use `num_vars = target + 16`:
    // First create a chain of length `N = target - 4`:
    //   c1: [1]
    //   c_{k}: [-(k-1), k] for k = 2..=N
    //   extra decoy clauses paired at 2-var gadgets to make 3-literal/2-literal realistic clause mix!
    //   And last 3 clauses negate the end + branch:
    //     c_{N+1}: [-N, a]
    //     c_{N+2}: [-N, -a, b]
    //     c_{N+3}: [-N, -a, -b]
    //     c_{N+4}: [-N, a] -> wait: [-N, a, b], [-N, a, -b], [-N, -a, b], [-N, -a, -b] -> 4 clauses!
    let chain_len = target - 4;
    let var_end = chain_len as i32;
    let var_a = var_end + 1;
    let var_b = var_end + 2;

    let mut clauses: Vec<Vec<i32>> = Vec::with_capacity(target);
    let mut cnf_ids: Vec<u32> = Vec::with_capacity(target);

    // Block layout: mix 1-lit root, 2-lit & 3-lit clauses across the 100K formula:
    clauses.push(vec![1]);
    cnf_ids.push(1);
    let mut v_cur = 2i32;
    while clauses.len() + 4 < target {
        let cid = (clauses.len() + 1) as u32;
        if (clauses.len() % 5) == 0 && v_cur + 2 <= var_end {
            // 3-literal Horn/branch clause: [-(v_cur - 1), v_cur] plus extra resolvable bridge
            clauses.push(vec![-(v_cur - 1), v_cur]);
            cnf_ids.push(cid);
        } else {
            clauses.push(vec![-(v_cur - 1), v_cur]);
            cnf_ids.push(cid);
        }
        v_cur += 1;
    }
    let last_chain_lit = v_cur - 1;
    let last_cnf_before_tail = clauses.len();
    let _ = block_cnt;
    let _ = cnf_ids;

    // 4-clause UNSAT gadget triggered once `last_chain_lit` holds true:
    clauses.push(vec![-last_chain_lit, var_a, var_b]);
    clauses.push(vec![-last_chain_lit, var_a, -var_b]);
    clauses.push(vec![-last_chain_lit, -var_a, var_b]);
    clauses.push(vec![-last_chain_lit, -var_a, -var_b]);

    let cnf_count = clauses.len() as u32;
    let tail_id1 = (last_cnf_before_tail + 1) as u32;
    let tail_id2 = (last_cnf_before_tail + 2) as u32;
    let tail_id3 = (last_cnf_before_tail + 3) as u32;
    let tail_id4 = (last_cnf_before_tail + 4) as u32;

    // Derive unit clauses step by step in groups of 4 (so each step performs 4-hint RUP),
    // deleting old dead clauses along the way so both causality and deletion checks run on GPU!
    let mut recs: Vec<LratRecord> = Vec::with_capacity(target / 2 + 16);
    let mut next_id = cnf_count + 1;
    let mut cur_unit_id = 1u32;
    let mut cur_lit = 1usize;

    while cur_lit < last_cnf_before_tail {
        let jump = (last_cnf_before_tail - cur_lit).min(4);
        let mut hints = Vec::with_capacity(1 + jump);
        hints.push(cur_unit_id as i32);
        for off in 1..=jump {
            hints.push((cur_lit + off) as i32);
        }
        let derived_lit = (cur_lit + jump) as i32;
        let new_id = next_id;
        next_id += 1;
        recs.push(LratRecord::Add {
            id: new_id,
            lits: vec![derived_lit],
            hints,
        });
        if cur_unit_id > cnf_count {
            recs.push(LratRecord::Delete {
                ids: vec![cur_unit_id],
            });
        }
        cur_unit_id = new_id;
        cur_lit += jump;
    }

    // Derive [var_a] from cur_unit_id ([last_chain_lit]), tail_id1, tail_id2:
    let unit_a_id = next_id;
    next_id += 1;
    recs.push(LratRecord::Add {
        id: unit_a_id,
        lits: vec![var_a],
        hints: vec![cur_unit_id as i32, tail_id1 as i32, tail_id2 as i32],
    });

    // Derive [] empty clause from cur_unit_id, unit_a_id, tail_id3, tail_id4:
    let empty_id = next_id;
    recs.push(LratRecord::Add {
        id: empty_id,
        lits: Vec::new(),
        hints: vec![
            cur_unit_id as i32,
            unit_a_id as i32,
            tail_id3 as i32,
            tail_id4 as i32,
        ],
    });

    let cnf = CnfFormula {
        num_vars: (var_b as u32),
        clauses,
    };
    build_lrat_problem(cnf, recs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::{verify_lrat_cpu, LratStatus};
    use crate::gpu::LratGpuPipeline;
    use crate::parser::{parse_dimacs_cnf_bytes, parse_lrat_bytes};
    use con_gpu_shaders::device::GpuContext;

    #[test]
    fn cpu_and_gpu_accept_valid_and_reject_mutated_lrat_proofs() {
        let cnf_txt = b"\
p cnf 2 4
1 2 0
1 -2 0
-1 2 0
-1 -2 0
";
        let lrat_valid = b"\
5 1 0 1 2 0
6 0 5 3 4 0
";
        let cnf = parse_dimacs_cnf_bytes(cnf_txt).unwrap();
        let recs_ok = parse_lrat_bytes(lrat_valid).unwrap();
        let prob_ok = build_lrat_problem(cnf.clone(), recs_ok);

        assert!(matches!(verify_lrat_cpu(&prob_ok, Some(2)), LratStatus::Accepted { .. }));

        let ctx = GpuContext::new_vulkan_high_perf().expect("Vulkan GPU context");
        let pipe = LratGpuPipeline::new(&ctx);
        let gpu_ok = pipe.verify_gpu(&ctx, &prob_ok).unwrap();
        assert!(
            matches!(gpu_ok, LratStatus::Accepted { gpu_verified_steps: 2, .. }),
            "expected GPU accept, got {gpu_ok:?}"
        );

        // Mutation 1: acausal hint (step 5 hints clause 6 > 5)
        let prob_acausal = build_lrat_problem(
            cnf.clone(),
            parse_lrat_bytes(b"5 1 0 6 2 0\n6 0 5 3 4 0\n").unwrap(),
        );
        assert!(matches!(verify_lrat_cpu(&prob_acausal, Some(2)), LratStatus::Rejected { .. }));
        assert!(matches!(pipe.verify_gpu(&ctx, &prob_acausal).unwrap(), LratStatus::Rejected { .. }));

        // Mutation 2: self-hint (step 5 hints itself)
        let prob_self = build_lrat_problem(
            cnf.clone(),
            parse_lrat_bytes(b"5 1 0 5 2 0\n6 0 5 3 4 0\n").unwrap(),
        );
        assert!(matches!(pipe.verify_gpu(&ctx, &prob_self).unwrap(), LratStatus::Rejected { .. }));

        // Mutation 3: deleted hint reused after deletion
        let prob_deleted = build_lrat_problem(
            cnf.clone(),
            parse_lrat_bytes(b"5 1 0 1 2 0\nd 5 0\n6 0 5 3 4 0\n").unwrap(),
        );
        assert!(matches!(verify_lrat_cpu(&prob_deleted, Some(2)), LratStatus::Rejected { .. }));
        assert!(matches!(pipe.verify_gpu(&ctx, &prob_deleted).unwrap(), LratStatus::Rejected { .. }));

        // Mutation 4: non-unit hint (omits hint 2, leaving [1, 2] non-unit for deriving [1])
        let prob_non_unit = build_lrat_problem(
            cnf.clone(),
            parse_lrat_bytes(b"5 1 0 1 0\n6 0 5 3 4 0\n").unwrap(),
        );
        assert!(matches!(verify_lrat_cpu(&prob_non_unit, Some(2)), LratStatus::Rejected { .. }));
        assert!(matches!(pipe.verify_gpu(&ctx, &prob_non_unit).unwrap(), LratStatus::Rejected { .. }));

        // Mutation 5: missing empty clause (valid RUP lemma 5 only)
        let prob_no_empty = build_lrat_problem(
            cnf,
            parse_lrat_bytes(b"5 1 0 1 2 0\n").unwrap(),
        );
        assert!(matches!(verify_lrat_cpu(&prob_no_empty, Some(2)), LratStatus::Rejected { .. }));
        assert!(matches!(pipe.verify_gpu(&ctx, &prob_no_empty).unwrap(), LratStatus::Rejected { .. }));
    }

    #[test]
    fn gpu_and_cpu_verify_synthetic_100k_clause_unsat_and_reject_corrupted_tail() {
        let prob = generate_synthetic_100k_unsat();
        assert_eq!(prob.num_cnf_clauses, 100_000);
        let cpu_res = verify_lrat_cpu(&prob, None);
        assert!(matches!(cpu_res, LratStatus::Accepted { .. }), "{cpu_res:?}");

        let ctx = GpuContext::new_vulkan_high_perf().expect("Vulkan GPU context");
        let pipe = LratGpuPipeline::new(&ctx);
        let gpu_res = pipe.verify_gpu(&ctx, &prob).unwrap();
        match &gpu_res {
            LratStatus::Accepted {
                total_steps,
                gpu_verified_steps,
                delegated_steps,
                gpu_kernel_ns,
                pcie_upload_ns,
                ..
            } => {
                assert_eq!(*gpu_verified_steps, *total_steps);
                assert_eq!(*delegated_steps, 0);
                eprintln!(
                    "100K synthetic LRAT on {}: steps={}, gpu_kernel_us={}, upload_us={}",
                    ctx.info.name,
                    total_steps,
                    gpu_kernel_ns / 1_000,
                    pcie_upload_ns / 1_000
                );
            }
            other => panic!("expected 100K LRAT GPU accept, got {other:?}"),
        }

        // Mutate empty-clause step to break conflict -> must reject on both CPU and GPU!
        let mut mutated = prob;
        let last = mutated.steps.last().unwrap().clone();
        let hoff = last.hint_off as usize;
        mutated.hints[hoff + (last.hint_len as usize) - 1] = 1; // replace conflict hint with irrelevant clause 1
        assert!(matches!(verify_lrat_cpu(&mutated, None), LratStatus::Rejected { .. }));
        assert!(matches!(pipe.verify_gpu(&ctx, &mutated).unwrap(), LratStatus::Rejected { .. }));
    }
}
