# `con-gpu` — Zero-Float GPU & Multi-Core Lean 4 Kernel + LRAT Verifier

`con-gpu` is a mathematically exact, zero-floating-point Lean 4 kernel typechecker, Reverse Unit Propagation (RUP) LRAT UNSAT proof checker/trimmer, batch arbitrary-width `Nat` bignum evaluator, and persistent Lake verification daemon built on Vulkan compute shaders (`wgpu` WGSL) and parallel `rayon` CPU execution.

## Architectural Guarantees

1. **Zero Floating-Point & Zero `u64`/`SHADER_INT64` in GPU Shaders**:
   - Every WGSL compute shader in `crates/con-gpu-shaders/src/wgsl/` and `crates/con-gpu-lrat/src/wgsl/` uses strictly `u32`, `i32`, `vec2<u32>`, integer shifts, and exact integer comparisons — no `f32`/`f64` operations and no `u64`/`i64` extensions anywhere in verification code.
   - Host checking uses exact arbitrary-width `u32`/`u64` integer arithmetic (`con-ron-core` and exact host LRAT/bignum evaluators), never floating-point computation.
2. **Exact Delegation Invariant (`STATUS_DELEGATE`)**:
   - GPU shaders verify declarations and LRAT clauses only when every required reduction, guard, and causal hint check matches Lean 4 kernel semantics exactly within per-lane step, continuation-stack, and scratch budgets (`max_steps`, `max_stack_frames`, `max_scratch_words`).
   - Any declaration or proof step outside the fast-path GPU model or budget sets `STATUS_DELEGATE` — **never** silently accepting — and is checked to completion concurrently or in fallback by the exact parallel host `con-ron-core` arena verifier (`HostExactRunner`) or host LRAT checker.
   - A GPU rejection (`STATUS_REJECTED_GPU`) is cross-checked on the host prefix up to the failure point and halts immediately with the exact verdict and reason.
3. **Strict Axiom Verification by Default (`--trust-bv-decide-axioms` Opt-In)**:
   - By default (`VerifyOptions::default()`, `trust_bv_decide_axioms = false`), non-standard axioms (including `bv_decide` certificate axioms) return `VerificationVerdict::Declined` (exit code `2`).
   - Passing `--trust-bv-decide-axioms` (or setting `CON_GPU_TRUST_BV_DECIDE=1`) enables exact structural validation for Lean 4 `bv_decide` certificate axioms: matches `._native.bv_decide.ax_<digits>(_digits)*` names with empty `level_params`, verifies constant basis pins (`and_pin_ok`), verifies the axiom type matches `Eq.{1} Bool (Std.Tactic.BVDecide.Reflect.verifyBVExpr ...) Bool.true`, and checks constant declarations structurally without delegating arbitrary non-standard axioms.

## Workspace Structure

- [`crates/con-gpu-arena`](crates/con-gpu-arena/Cargo.toml):
  - `loader.rs`: Two-phase `.olean` compact-region + NDJSON loader producing a frozen `LoadedEnvironment` backed by `con-ron-core`'s 32-bit `PersTier` arena (`build_olean_input`, `load_environment`, `load_environment_with_fs`, `load_environment_with_fs_and_base`), with `--base-olean` prefix tracking (`preverified_prefix`) and WSL2 `/mnt/<drive>/...` path normalization on Windows.
  - `fs.rs`: Windows/WSL2-safe `StdFs` and thread-safe in-memory `CachedFs` implementing `con_ron_core::arena::io::OleanFs`, multi-threaded `.olean` closure prefetch + hashing (`prefetch_olean_closure`), `compute_closure_fingerprint`, `normalize_wsl_mnt_path`, `normalize_lean_path_str`, `normalize_lean_path`, `split_search_path`, and `resolve_olean_file`.
  - `soa_pack.rs`: Packs frozen `PersTier` expression/level nodes, DAG guard summaries, declaration records, and CSR environment tables into `u32` GPU storage buffers (`e_nodes` paged up to `8 GiB` via `E_NODES_PAGE_WORDS = 1 << 28` across 8 bindings `e_nodes_0..e_nodes_7`, `meta_nodes`, `env_tables`, `jobs`), validating 26-bit/30-bit/32-bit bounds cleanly (`try_pack_arena_from`), flagging all reserved/kernel-pinned literal/trust names (`JOB_FLAG_SPECIAL`), supporting incremental prefix skipping (`pack_arena_from`), and sorting eligible declaration jobs by `(ast_bucket, priority(Thm < Opaque < Defn))` for wavefront coherence.
  - `snapshot.rs`: Columnar bulk `bytemuck` binary snapshot format (`CGSNAP03`, `SNAPSHOT_MAGIC`) storing both the pre-packed `GpuArenaPacket` SoA buffers and the self-contained `HostEnvImage` (`PersTier` tables, `Pins`, `ipins`, `decls`, `module_hashes`) plus a sorted `.olean` stat+hash manifest `(norm_key, byte_len, mtime_secs, mtime_nanos, content_hash128)`. Validates closure via parallel `fs::metadata` (re-hashing bytes only on `mtime` mismatch or `--verify-olean-hashes`), verifies parallel `64 MiB`-chunked 128-bit integrity checksums BEFORE GPU launch, and uses zero-copy `Arc<Vec<u8>>` backing (`load_snapshot_gpu_first_with_overlap` / `SnapshotHostDecoder`) to overlap host `PersTier`/`ConsMap` decoding directly with GPU verification (`load_snapshot_for_cpu` for CPU-only snapshot checks).
  - `verify_host.rs`: Multi-core `rayon` wrapper over `con-ron-core` (`VerifyOptions`, `verify_host_parallel_with`, `verify_host_range_with`, `verify_delegated_exact_with`, `HostExactRunner` with persistent per-worker `WorkerCtx`, `StructuralPrefixCmp`, `matching_verified_prefix_len`, exact `bv_decide` axiom validation), honoring `RAYON_NUM_THREADS`.
- [`crates/con-gpu-shaders`](crates/con-gpu-shaders/Cargo.toml):
  - `device.rs`: Selects Vulkan `PowerPreference::HighPerformance` with full `adapter.limits()` (`GpuContext::shared_vulkan_high_perf` / `new_vulkan_high_perf`) for large storage buffer bindings.
  - `typecheck.rs` + `wgsl/typecheck_{arena,level,whnf,defeq,infer,fused,compact}.wgsl`: **Pipeline A** (`TypecheckGpuPipeline`) — `@workgroup_size(64)` persistent-register WGSL compute VM + worklist compaction across Tier 1 and Tier 2 scratch budgets (`verify_packet_hybrid_range_with`, `verify_packet_gpu_range_with`, `verify_snapshot_hybrid_owning_with`, `verify_snapshot_hybrid_with`), with eager 0-branch `1 GiB` `vm_1gb` (`E_NODES_PAGED = false`), lazy `8 GiB` paged `vm_paged` (`E_NODES_PAGED = true` via `e_read` across `e_nodes_0..e_nodes_7`), `phase 3u` `ETAG_APP` re-peel in `exec_whnf_core` (handling projected partial recursors such as `Quot.lift`), 2,048-bit (`<= 64`-limb) exact `BigNat` arithmetic (`succ`/`pred`/`add`/`sub`/`mul`/`beq`/`ble`/`land`/`lor`/`xor`) + exact `BigNat`/`String` literal equality & inference, depth-keyed workgroup defeq memoization, exact `u32`/`vec2<u32>` `Nat.pow`/`Nat.gcd` (`bhi != 0u` delegation), 0-field structure `caps.eta`, same-head spine congruence across hints, fast-bail heavy-bucket cutoffs + `tier2 >= 1,024` gating, early host/GPU arena buffer release before final host join, and streaming GPU/CPU delegation.
  - `bignum_nat.rs` + `wgsl/bignum_nat.wgsl`: **Pipeline B** (`BignumNatPipeline`) — exact base-$2^{32}$ multi-limb `Nat` GPU compute kernel supporting `Add`, `Sub` (saturating `Nat.sub`), `Mul` (via 16-bit split `mul32_wide`), `Cmp`, `Beq`, and `Ble`.
- [`crates/con-gpu-lrat`](crates/con-gpu-lrat/Cargo.toml):
  - `parser.rs`, `trim.rs`, `cpu.rs`, `gpu.rs`, `synth.rs`, `wgsl/lrat_verify.wgsl`: **Pipeline C** (`LratGpuPipeline`) — parses ASCII and binary LEB128 `.lrat` proofs (rejecting explicit RAT hints cleanly), provides backward reachability cone trimming with last-use `d` deletions (`trim_lrat`, `format_lean_ascii_lrat`), and verifies RUP steps in parallel on GPU (`lds_table` 4,096 `i32` slots across 64 lanes x 64 slots) with exact `rayon` CPU fallback (`verify_lrat_cpu`).
- [`crates/con-gpu-cli`](crates/con-gpu-cli/Cargo.toml):
  - `main.rs`: CLI (`con-gpu`) exposing `verify`, `check-lrat`, `trim-check-lrat`, `test-soundness`, `daemon`, and `bench`.

## Build & Test

```powershell
cargo build --release --manifest-path con-gpu/Cargo.toml --bin con-gpu
cargo test --release --manifest-path con-gpu/Cargo.toml --workspace -- --test-threads=1
```

## CLI Subcommands & Daemon Protocol

- `con-gpu verify <olean-or-ndjson-paths...> [--backend gpu|cpu|hybrid] [--jobs N] [--load-paths dir1;dir2] [--no-materialize] [--trust-bv-decide-axioms] [--base-olean <path>] [--save-snapshot <path>] [--snapshot <path>] [--verify-olean-hashes] [--daemon[=addr] | --daemon-addr addr] [--queue] [--flush] [--fresh]`
  - Ingests `LEAN_PATH` and normalizes `/mnt/<drive>/...` WSL2 paths automatically.
  - `--base-olean <path>` skips the verified import prefix (`matching_verified_prefix_len` / `preverified_prefix`); `--save-snapshot <path>` writes a `CGSNAP03` dual-arena columnar snapshot on `Accepted`; `--snapshot <path>` verifies a `CGSNAP03` snapshot on `hybrid`, `gpu`, or `cpu` (`load_snapshot_for_cpu`) after validating the sorted `.olean` stat+hash manifest (stat-fast `mtime`+size check by default, or full byte re-hash via `--verify-olean-hashes`) and parallel `64 MiB`-chunked 128-bit integrity checksum, with zero `.olean` compact-region re-parsing.
  - Offloads automatically when `CON_GPU_DAEMON_ADDR` is set (unless `--fresh`, `--snapshot`, `--save-snapshot`, or `--base-olean` is passed); supports queued batching via `--queue` / `CON_GPU_BATCH_QUEUE=1` and `--flush`.
- `con-gpu check-lrat <cnf> <lrat> [--backend gpu|cpu] [--threads N]`
- `con-gpu trim-check-lrat <cnf> <lrat> [<out_txt> | --out <trimmed.lrat|->] [--no-trim] [--backend gpu|cpu] [--threads N] [--daemon[=addr] | --daemon-addr addr] [--fresh]`
  - Trims dead clauses from text or binary LRAT proofs (unless `--no-trim`), verifies the resulting proof first, and writes output only on `Accepted` (`--out -` streams trimmed ASCII LRAT to stdout and writes telemetry to stderr; negative RAT steps are declined).
- `con-gpu test-soundness [--e2e-limit N]`
- `con-gpu daemon --addr 127.0.0.1:<port> [--base-olean <path>] [--no-gpu] [--trust-bv-decide-axioms]`
  - Maintains a persistent `CachedFs`, startup-verifies `--base-olean` before binding, and caches its `LoadedEnvironment` prefix (`matching_verified_prefix_len` / `preverified_prefix`) to skip already-verified imports on subsequent `VERIFY` / `FLUSH_VERIFY` requests.
  - Line-oriented TCP protocol: `PING`, `STATS`, `VERIFY`, `QUEUE_VERIFY`, `FLUSH_VERIFY`, `CHECK_LRAT`, `TRIM_CHECK_LRAT`, and `SHUTDOWN`.
- `con-gpu bench [--threads N] [--skip-leanchecker]`

## Observed Verification & Benchmark Results (Phase 6 — Wave V2 + V2.1)

All results below were measured after the final Wave V2 + V2.1 code edits on Windows 11 with **AMD Radeon RX 7900 XTX** (`backend=Vulkan`, `max_storage=2147483644`, driver `26.8.1 (LLPC)`), 16 host logical processors, and Lean `v4.35.0`. Artifact JSONs, logs, and `sha256sums.txt` live under `benchmarks/aws_ecosystem_phase6/local_rx7900xtx/`.

### Release Test Suite (`cargo test --workspace --manifest-path con-gpu/Cargo.toml --release -- --test-threads=1`)

**`39 passed; 0 failed`** across all 5 test suites (`EXIT=0`):

- `con-gpu-arena` (`lib`): `16 passed; 0 failed`
- `con-gpu-arena` (`init_smoke`): `3 passed; 0 failed`
- `con-gpu` (`con-gpu-cli`): `6 passed; 0 failed` — includes `CGSNAP03` save/load/tamper, `--backend cpu --snapshot`, and `--verify-olean-hashes --snapshot`.
- `con-gpu-lrat`: `6 passed; 0 failed`
- `con-gpu-shaders`: `8 passed; 0 failed` — includes `paged_e_nodes_8gb_reader_handles_page_crossing_above_2_28` and `gpu_bignat_256bit_and_string_lit_equality_without_delegation` (`delegated_count == 0`).

### CLI Soundness Suite (`con-gpu.exe test-soundness`, `EXIT=0`)

Logged in `benchmarks/aws_ecosystem_phase6/local_rx7900xtx/test_soundness_rx7900xtx.log`:

```text
Running con-gpu soundness suite on AMD Radeon RX 7900 XTX (backend=Vulkan)
[PASS] Pipeline B bignum_nat exact batch tests: 40/40 ops matched
[PASS] Pipeline C LRAT fixtures (GPU & CPU differential): 3 accepted, 7 rejected
[PASS] Corrupt .olean files rejected: 4/4
[PASS] Pipeline A con-leche differential soundness: tested=587 accepted=341 rejected=246 gpu_verified=17670 gpu_rejected=128 delegated=13669
```

*(Note: `test-soundness` skips non-default `nat_size_limit` non-zero limit cases and `code == 124` infinite-loop fixtures, exempts `*sorry*` fixtures from expected exit-code parity, and asserts `gpu_code == host_code` across all `587` tested `con-leche` fixtures.)*

### Synthetic BignumNat & LRAT Benchmarks (`con-gpu.exe bench-synthetic --backend both --threads 16`, `EXIT=0`)

Recorded in `benchmarks/aws_ecosystem_phase6/local_rx7900xtx/bench_synthetic_rx7900xtx.json` (`all_passed: true`):

| Pipeline / Scale | Parity / Coverage | GPU Total (ms) | CPU Rayon 16-Thread (ms) |
|---|---|---:|---:|
| Pipeline B `BignumNat` (`ops=16,384`) | `100%` exact parity | `11.022` (`upload=0.384`, `kernel=1.323`) | `1.210` |
| Pipeline B `BignumNat` (`ops=65,536`) | `100%` exact parity | `6.963` (`upload=1.264`, `kernel=0.572`) | `3.458` |
| Pipeline B `BignumNat` (`ops=262,144`) | `100%` exact parity | `20.373` (`upload=1.806`, `kernel=0.878`) | `8.567` |
| Pipeline C LRAT (`100,000` clauses, `25,001` steps) | `delegated=0`, `corrupt_rejected=(gpu:true, cpu:true)` | `1.913` (`upload=0.891`, `kernel=0.613`) | `21.063` |
| Pipeline C LRAT (`500,000` clauses, `125,001` steps) | `delegated=0`, `corrupt_rejected=(gpu:true, cpu:true)` | `6.225` (`upload=3.969`, `kernel=1.500`) | `52.322` |
| Pipeline C LRAT (`1,000,000` clauses, `250,001` steps) | `delegated=0`, `corrupt_rejected=(gpu:true, cpu:true)` | `12.315` (`upload=8.132`, `kernel=2.693`) | `66.067` |

### RX 7900 XTX benchmarks before the Phase 6 shader correction (16 threads)

In this run the CPU and hybrid modes agreed on verdict, exit code, and declaration count. The hybrid run recorded one GPU rejection for `PrimeNumberTheoremAnd`.

On the final shared inputs, Full Mathlib accepted 775,321 declarations. `PrimeNumberTheoremAnd` declined at declaration 528,744 for `sorryAx`. The corrected RX, L40S and A10G runs recorded zero GPU rejections. [Final Phase 6 benchmark report](../benchmarks/ECOSYSTEM_BENCHMARK_REPORT.md)

| Repo / Workload | Decls | Verdict (`exit`) | `cpu_cold` Wall | `hybrid_cold` Wall | `cpu_snap` Wall | `hybrid_snap` Wall | Hybrid GPU Verified |
|---|---:|---|---:|---:|---:|---:|---:|
| `Full_Mathlib` | `775,326` | `Accepted` (`0`) | `320.93 s` (`load=192.39s, verify=128.53s`) | `321.45 s` (`load=177.84s, verify=143.17s, gpu=30.58s, fallback=98.16s`) | `152.56 s` (`load=35.74s, verify=116.82s`) | **`146.98 s`** (`load=2.99s, pcie=1.09s, gpu=23.34s, fallback=118.80s, verify=143.77s`) | `240,185` (`gpu_rej=0`) |
| `Mathlib_Real_Basic` | `217,474` | `Accepted` (`0`) | `49.58 s` | `35.83 s` | `15.16 s` | **`14.48 s`** | `94,940` cold / `130,568` snap (`gpu_rej=0`) |
| `DownstreamBench` | `114,770` | `Accepted` (`0`) | `27.99 s` | `24.53 s` | `13.61 s` | **`12.77 s`** | `58,948` (`gpu_rej=0`) |
| `Init_Std` | `113,257` | `Accepted` (`0`) | `36.95 s` | `28.26 s` | `13.28 s` | `13.75 s` | `58,303` (`gpu_rej=0`) |
| `SyntheticBench` | `117,461` | `Accepted` (`0`) | `27.59 s` | `32.04 s` | `14.80 s` | `18.47 s` | `59,476` cold / `59,474` snap (`gpu_rej=0`) |
| `Cedar` | `173,475` | `Declined` (`2`) | `41.16 s` | `42.55 s` | — | — | `101,573` (`gpu_rej=0`) |
| `PrimeNumberTheoremAnd` | `544,714` | `Declined` (`2`) | `167.95 s` | `197.25 s` | — | — | `219,622` (`gpu_rej=1` folded behind earlier `sorryAx` decl) |
