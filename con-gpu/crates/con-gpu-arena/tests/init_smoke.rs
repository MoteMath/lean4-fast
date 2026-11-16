use std::path::Path;

use con_gpu_arena::loader::{build_olean_input, load_environment, VerificationVerdict};
use con_gpu_arena::soa_pack::{pack_arena, ArenaLimitsConfig};
use con_gpu_arena::verify_host::verify_host_parallel;

#[test]
fn load_pack_and_host_verify_sample_fixtures() {
    let fixture_ok = Path::new("c:/Users/devin/Desktop/lean/vendor/con-leche/tests/e2e/t_add_zero.ndjson");
    if fixture_ok.exists() {
        let env = load_environment(&con_gpu_arena::loader::InputSpec::Ndjson {
            path: fixture_ok.to_path_buf(),
        })
        .expect("t_add_zero should load");
        let (verdict, tel) = verify_host_parallel(&env, Some(4));
        assert!(matches!(verdict, VerificationVerdict::Accepted { .. }), "{verdict:?}");
        let pkt = pack_arena(&env, ArenaLimitsConfig::default());
        assert_eq!(pkt.jobs.len(), env.decls.len());
        eprintln!(
            "fixture t_add_zero: decls={}, eligible={}, host_us={}, pack_us={}",
            env.decls.len(),
            pkt.eligible_jobs_count,
            tel.elapsed_ns / 1_000,
            pkt.pack_ns / 1_000,
        );
    }
}

#[test]
fn load_and_host_verify_init_if_installed() {
    let init_path = "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init.olean";
    if !Path::new(init_path).exists() {
        return;
    }
    let spec = build_olean_input(&[init_path.to_string()], &[], None, false);
    let env = load_environment(&spec).expect("Init should load");
    let pkt = pack_arena(&env, ArenaLimitsConfig::default());
    let (verdict, tel) = verify_host_parallel(&env, None);
    assert!(matches!(verdict, VerificationVerdict::Accepted { .. }), "{verdict:?}");
    eprintln!(
        "Init (lazy): decls={}, eligible={}, load_ms={}, index_ms={}, pack_ms={}, host_ms={}, threads={}",
        env.decls.len(),
        pkt.eligible_jobs_count,
        env.load_ns / 1_000_000,
        env.index_ns / 1_000_000,
        pkt.pack_ns / 1_000_000,
        tel.elapsed_ns / 1_000_000,
        tel.thread_count
    );
}

#[test]
fn load_and_pack_init_materialized_if_installed() {
    let init_path = "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init.olean";
    if !Path::new(init_path).exists() {
        return;
    }
    let spec = build_olean_input(&[init_path.to_string()], &[], None, true);
    let env = load_environment(&spec).expect("Init materialized should load");
    let pkt = pack_arena(&env, ArenaLimitsConfig::default());
    eprintln!(
        "Init (materialized): decls={}, thm_mat={}, eligible={}, load_ms={}, mat_ms={}, index_ms={}, pack_ms={}, e_nodes_words={}",
        env.decls.len(),
        env.thm_materialized_count,
        pkt.eligible_jobs_count,
        env.load_ns / 1_000_000,
        env.materialize_ns / 1_000_000,
        env.index_ns / 1_000_000,
        pkt.pack_ns / 1_000_000,
        pkt.e_nodes.len(),
    );
    assert!(pkt.eligible_jobs_count > 50_000, "expected >50k eligible jobs on materialized Init, got {}", pkt.eligible_jobs_count);
}
