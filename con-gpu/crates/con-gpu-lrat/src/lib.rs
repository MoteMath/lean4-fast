//! Exact parallel LRAT UNSAT proof verifier (CPU rayon + GPU WGSL).

pub mod cpu;
pub mod gpu;
pub mod parser;
pub mod synth;
pub mod trim;

pub use cpu::{verify_lrat_cpu, LratStatus};
pub use gpu::LratGpuPipeline;
pub use parser::{
    build_lrat_problem, load_lrat_files, parse_dimacs_cnf_bytes, parse_lrat_bytes, CnfFormula,
    LratProblem, LratRecord,
};
pub use synth::{generate_synthetic_100k_unsat, generate_synthetic_unsat};
pub use trim::{format_lean_ascii_lrat, trim_lrat, trim_lrat_records, TrimStats, TrimmedLrat};
