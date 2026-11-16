pub mod fs;
pub mod loader;
pub mod snapshot;
pub mod soa_pack;
pub mod verify_host;

pub use fs::{
    compute_chunked_checksum128, compute_closure_fingerprint, normalize_closure_roots,
    prefetch_olean_closure, validate_closure_manifest, CachedFs, CachedFsStats, ClosureTarget,
    PrefetchedClosure, PrefetchedOleanFile, SnapshotManifestEntry,
};
pub use loader::{
    load_environment, load_environment_from_prefix, load_environment_with_fs,
    load_environment_with_fs_and_base, InputSpec, LoadedEnvironment, VerificationVerdict,
};
pub use snapshot::{
    load_snapshot, load_snapshot_for_cpu, load_snapshot_gpu_first,
    load_snapshot_gpu_first_with_overlap, save_snapshot, CpuLoadedSnapshot, GpuFirstSnapshot,
    LoadedSnapshot, SNAPSHOT_MAGIC,
};
pub use soa_pack::{
    pack_arena, pack_arena_from, ArenaHeader, ArenaLimitsConfig, GpuArenaPacket, GpuJob,
    GpuVerdict, JobKind, E_NODES_NUM_PAGES, E_NODES_PAGE_WORDS, MAX_BIGNAT_LIMBS,
    MAX_E_NODES_WORDS, STATUS_DELEGATE, STATUS_REJECTED_GPU, STATUS_VERIFIED_GPU,
};
pub use verify_host::{
    check_job_exact, check_job_exact_with, matching_verified_prefix_len, verify_delegated_exact,
    verify_delegated_exact_with, verify_host_parallel, verify_host_parallel_with,
    verify_host_range_with, HostExactRunner, HostTelemetry, VerifyOptions,
};
