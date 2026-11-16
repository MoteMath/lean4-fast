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
  - `snapshot.rs`: Columnar bulk `bytemuck` binary snapshot format (`CGSNAP03`, `SNAPSHOT_MAGIC`) storing both the pre-packed `GpuArenaPacket` SoA buffers and the self-contained `HostEnvImage` (`PersTier` tables, `Pins`, `ipins`, `decls`, `module_hashes`) plus a sorted `.olean` stat+hash manifest `(norm_key, byte_len, mtime_secs, mtime_nanos, content_hash128)`. Validates closure via parallel `fs::metadata` (re-hashing bytes only on `mtime` mismatch or `--verify-olean-hashes`) and verifies parallel `64 MiB`-chunked 128-bit integrity checksums BEFORE GPU launch (`load_snapshot_gpu_first` + `split_for_hybrid`) or CPU `load_snapshot_for_cpu`, overlapping GPU verification with parallel `PersTier`/`ConsMap` index reconstruction.
  - `verify_host.rs`: Multi-core `rayon` wrapper over `con-ron-core` (`VerifyOptions`, `verify_host_parallel_with`, `verify_host_range_with`, `verify_delegated_exact_with`, `HostExactRunner`, `StructuralPrefixCmp`, `matching_verified_prefix_len`, exact `bv_decide` axiom validation), honoring `RAYON_NUM_THREADS`.
- [`crates/con-gpu-shaders`](crates/con-gpu-shaders/Cargo.toml):
  - `device.rs`: Selects Vulkan `PowerPreference::HighPerformance` with full `adapter.limits()` (`GpuContext::shared_vulkan_high_perf` / `new_vulkan_high_perf`) for large storage buffer bindings.
  - `typecheck.rs` + `wgsl/typecheck_{arena,level,whnf,defeq,infer,fused,compact}.wgsl`: **Pipeline A** (`TypecheckGpuPipeline`) — `@workgroup_size(64)` persistent-register WGSL compute VM + worklist compaction across Tier 1 and Tier 2 scratch budgets (`verify_packet_hybrid_range_with`, `verify_packet_gpu_range_with`, `verify_snapshot_hybrid_with`), with eager 0-branch `1 GiB` `vm_1gb` (`E_NODES_PAGED = false`) and lazy `8 GiB` paged `vm_paged` (`E_NODES_PAGED = true` via `e_read` across `e_nodes_0..e_nodes_7`), 2,048-bit (`<= 64`-limb) exact `BigNat` arithmetic (`succ`/`pred`/`add`/`sub`/`mul`/`beq`/`ble`/`land`/`lor`/`xor`) + exact `BigNat`/`String` literal equality & inference, depth-keyed workgroup defeq memoization, exact `u32`/`vec2<u32>` `Nat.pow`/`Nat.gcd` (`bhi != 0u` delegation), 0-field structure `caps.eta`, same-head spine congruence across hints, and two-ended GPU/CPU work-stealing.
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

## Observed Verification & Benchmark Results (Wave N)

All results below were measured after the final Wave N workspace edits on Windows 11 with **AMD Radeon RX 7900 XTX** (`backend=Vulkan`, `max_storage=2147483644`), 16 host logical processors, and Lean `v4.35.0`.

### Build & Static Checks

- Release profile (`Cargo.toml`): `opt-level = 3`, `lto = false`, `codegen-units = 16`, `overflow-checks = true`.
- Release binary (`target/release/con-gpu.exe`): `11,212,800` bytes.
- Zero-float scan (`rg -n "\b(f16|f32|f64|float|from_bits|to_bits)\b" con-gpu/crates/`): matched only `5` comment/doc lines (`soa_pack.rs:86`, `lrat_verify.wgsl:2`, `bignum_nat.wgsl:2`, `typecheck_arena.wgsl:1`, `typecheck_arena.wgsl:2`); zero floating-point types, casts, or operations in any verification path.
- Zero-64-bit WGSL scan (`rg -n "\b(u64|i64)\b|SHADER_INT64"` across `crates/con-gpu-{shaders,lrat}/src/wgsl/`): matched only `6` comment lines (`lrat_verify.wgsl:2`, `bignum_nat.wgsl:2`, `typecheck_whnf.wgsl:1`, `typecheck_whnf.wgsl:499`, `typecheck_whnf.wgsl:616`, `typecheck_arena.wgsl:2`).
- `vendor/con-ron`: untouched (`git -C vendor/con-ron status -s` clean).

### Release Test Suite (`cargo test --workspace --manifest-path con-gpu/Cargo.toml --release -- --test-threads=1`)

**`38 passed; 0 failed`** across all 5 test suites (`EXIT=0`, zero warnings):

- `con-gpu-arena` (`lib`): `16 passed; 0 failed` (`3.49 s`)
- `con-gpu-arena` (`init_smoke`): `3 passed; 0 failed` (`29.13 s`)
- `con-gpu-cli`: `5 passed; 0 failed` (`21.33 s`) — includes `CGSNAP03` save/load/tamper, `--backend cpu --snapshot`, and `--verify-olean-hashes --snapshot`.
- `con-gpu-lrat`: `6 passed; 0 failed` (`0.40 s`)
- `con-gpu-shaders`: `8 passed; 0 failed` (`42.14 s`) — includes `paged_e_nodes_8gb_reader_handles_page_crossing_above_2_28` and `gpu_bignat_256bit_and_string_lit_equality_without_delegation` (`delegated_count == 0`).

### CLI Soundness Suite (`con-gpu.exe test-soundness`, `EXIT=0`)

```text
Running con-gpu soundness suite on AMD Radeon RX 7900 XTX (backend=Vulkan)
[PASS] Pipeline B bignum_nat exact batch tests: 40/40 ops matched
[PASS] Pipeline C LRAT fixtures (GPU & CPU differential): 3 accepted, 7 rejected
[PASS] Corrupt .olean files rejected: 4/4
[PASS] Pipeline A con-leche differential soundness: tested=587 accepted=341 rejected=246 gpu_verified=17691 gpu_rejected=128 delegated=13648
```

*(Note: `test-soundness` skips non-default `nat_size_limit` non-zero limit cases and `code == 124` infinite-loop fixtures, exempts `*sorry*` fixtures from expected exit-code parity, and asserts `gpu_code == host_code` across all `587` tested `con-leche` fixtures.)*

### Benchmarks (`con-gpu.exe bench --threads 16 --skip-leanchecker`, `EXIT=0`)

*(Run with `--skip-leanchecker` across 16 host threads.)*

| Workload | Verdict / Notes | GPU Hybrid (ms) | CPU Rayon 16-Thread (ms) |
|---|---|---:|---:|
| Lean `Init` (`63,937` decls, `63,306` eligible, `28,066` GPU / `35,871` delegated) | `Accepted` (`load=9388.474`, `pack=573.855`) | `6487.782` (`upload=71.919`, `kernel=5984.509`, `readback=83.842`, `fallback=345.753`) | `6279.328` |
| Lean `Std` (`109,213` decls, `108,156` eligible, `41,099` GPU / `68,114` delegated) | `Accepted` (`load=18551.202`, `pack=1339.950`) | `10631.980` (`upload=239.949`, `kernel=9937.340`, `readback=326.314`, `fallback=126.168`) | `10600.188` |
| `DownstreamBench` strict (`114,770` decls, `113,636` eligible, `42,854` GPU / `71,916` delegated) | `Declined@114126` (`bv_decide` axiom) | `11559.444` (`upload=232.965`, `kernel=10994.642`, `readback=245.558`, `fallback=84.195`) | `11206.214` |
| `DownstreamBench --trust-bv-decide-axioms` (`114,770` decls, `113,636` eligible, `43,246` GPU / `71,524` delegated) | `Accepted` (`load=20469.596`, `pack=1191.352`) | `10939.464` (`upload=148.453`, `kernel=10348.646`, `readback=360.798`, `fallback=79.126`) | `9424.183` |
| Synthetic 100K LRAT (`cnf=100000`, `steps=25001`) | `verified=25001`, `delegated=0` | `3.055` (`upload=1.254`, `kernel=1.067`) | `42.960` |
| Pipeline B `BignumNat` (`batch_ops=16384`) | Exact `u32` limb batch | `gpu_kernel=0.619` | — |
| Incremental `--base-olean Init/Prelude -> Init` (`delta=61,935`, `prefix_skipped=2,002`) | `Accepted` (`26,269` GPU / `35,666` delegated; `end_to_end=16153.825`) | `inc_verify=5943.501` (`inc_load=9630.476`, `inc_pack=579.848`, `kernel=5744.020`, `fallback=44.491`) | — |
| Pre-Packed `CGSNAP03` Snapshot `--snapshot Init` (`211.66 MiB`, `28,847` GPU / `35,090` delegated) | `Accepted` (`total_hybrid_e2e=8574.422`) | `snap_verify=8333.497` (`save=429.402`, `snap_gpu_load=240.924`, `kernel=8057.980`, `fallback=64.150`) | `cpu_snap_load=2118.047`, `cpu_verify=6813.961` |
| Incremental `--base-olean Std -> DownstreamBench` (`delta=110,790`, `prefix_skipped=3,980`) | `Accepted` (`40,754` GPU / `70,036` delegated; `end_to_end=21809.458`) | `inc_verify=8151.667` (`inc_load=12717.863`, `inc_pack=939.927`, `kernel=7893.588`, `fallback=60.409`) | — |

```text
=== con-gpu Benchmark on AMD Radeon RX 7900 XTX (backend=Vulkan, max_storage=2147483644) ===
Bench Init: verdict=Accepted decls=63937 eligible=63306 gpu_verified=28066 delegated=35871 load=9388.474 ms pack=573.855 ms
  GPU hybrid: pcie_upload=71.919 ms gpu_kernel=5984.509 ms gpu_readback=83.842 ms host_fallback=345.753 ms total=6487.782 ms (steps_gpu=81272198, max_scratch=17070, delegate_reasons=[0, 631, 767, 6585, 0, 0, 27888, 0])
  CPU rayon (threads=16): verify=6279.328 ms
Bench Std: verdict=Accepted decls=109213 eligible=108156 gpu_verified=41099 delegated=68114 load=18551.202 ms pack=1339.950 ms
  GPU hybrid: pcie_upload=239.949 ms gpu_kernel=9937.340 ms gpu_readback=326.314 ms host_fallback=126.168 ms total=10631.980 ms (steps_gpu=139674004, max_scratch=20458, delegate_reasons=[0, 1057, 1083, 8934, 0, 0, 57040, 0])
  CPU rayon (threads=16): verify=10600.188 ms
Bench DownstreamBench (strict): verdict=Declined@114126 (non-standard axiom (DownstreamBench.BV.alu_avg_floor._native.bv_decide.ax_1_5), apparently added by the `bv_decide` tactic; con-leche does not support such axioms at the moment) decls=114770 eligible=113636 gpu_verified=42854 delegated=71916 load=20469.596 ms pack=1191.352 ms
  GPU hybrid: pcie_upload=232.965 ms gpu_kernel=10994.642 ms gpu_readback=245.558 ms host_fallback=84.195 ms total=11559.444 ms (steps_gpu=138720940, max_scratch=20562, delegate_reasons=[0, 1134, 1118, 7104, 0, 0, 62560, 0])
  CPU rayon (threads=16): verify=11206.214 ms
Bench DownstreamBench (--trust-bv-decide-axioms): verdict=Accepted decls=114770 eligible=113636 gpu_verified=43246 delegated=71524 load=20469.596 ms pack=1191.352 ms
  GPU hybrid: pcie_upload=148.453 ms gpu_kernel=10348.646 ms gpu_readback=360.798 ms host_fallback=79.126 ms total=10939.464 ms (steps_gpu=144926308, max_scratch=20562, delegate_reasons=[0, 1134, 1147, 8731, 0, 0, 60512, 0])
  CPU rayon (threads=16): verify=9424.183 ms
Bench 100K Synthetic LRAT (cnf=100000, steps=25001):
  GPU: verified=25001 delegated=0 pcie_upload=1.254 ms gpu_kernel=1.067 ms total=3.055 ms
  CPU rayon (threads=16): total=42.960 ms
Bench Pipeline B BignumNat: batch_ops=16384 gpu_kernel=0.619 ms
Bench Incremental (--base-olean Init/Prelude -> Init): decls=63937 prefix_skipped=2002 delta_decls=61935 eligible=61449 gpu_verified=26269 delegated=35666
  inc_load=9630.476 ms inc_pack=579.848 ms pcie_upload=25.054 ms gpu_kernel=5744.020 ms host_fallback=44.491 ms inc_verify=5943.501 ms end_to_end=16153.825 ms (fs_hits=4538, fs_misses=1959)
Bench Pre-Packed Snapshot (--snapshot Init): size_mib=211.66 decls=63937 eligible=63306 gpu_verified=28847 delegated=35090
  save=429.402 ms snap_gpu_load=240.924 ms pcie_upload=28.863 ms gpu_kernel=8057.980 ms host_fallback=64.150 ms snap_verify=8333.497 ms total_hybrid_e2e=8574.422 ms | cpu_snap_load=2118.047 ms cpu_verify=6813.961 ms
Bench Incremental (--base-olean Std -> DownstreamBench): decls=114770 prefix_skipped=3980 delta_decls=110790 eligible=109873 gpu_verified=40754 delegated=70036
  inc_load=12717.863 ms inc_pack=939.927 ms pcie_upload=98.863 ms gpu_kernel=7893.588 ms host_fallback=60.409 ms inc_verify=8151.667 ms end_to_end=21809.458 ms (fs_hits=17977, fs_misses=3474)
```

### Mathlib `v4.35.0` (`Mathlib.Data.Real.Basic` & Full `Mathlib`, RX 7900 XTX)

Run with `--fresh --jobs 16 --trust-bv-decide-axioms` against the Lean `v4.35.0` Mathlib `.olean` closures on the local AMD Radeon RX 7900 XTX (`24 GiB` VRAM, `max_storage=2147483644` bytes):

| Workload / Mode | Verdict / Coverage | Load (ms) | Verify (ms) | Notes |
|---|---|---:|---:|---|
| `Mathlib.Data.Real.Basic` (`217,474` decls) `--backend cpu --jobs 16` | `Accepted` | `25,253.381` | `9,832.769` | Cold `.olean` 16-thread host baseline |
| `Mathlib.Data.Real.Basic` `--backend hybrid --jobs 16 --save-snapshot` | `Accepted` (`214,460` eligible, `93,428` GPU / `124,046` delegated) | `23,457.291` | `11,478.865` (`upload=224.851`, `kernel=9,102.619`, `readback=249.463`, `fallback=333.236`) | Saves `501.05 MiB` `CGSNAP03` (`e_nodes_words=57,150,658`) |
| `Mathlib.Data.Real.Basic` `--backend hybrid --jobs 16 --snapshot` | `Accepted` (`99,395` GPU / `118,079` delegated) | `584.337` | `12,219.551` (`upload=153.543`, `kernel=11,645.472`, `readback=87.421`, `fallback=246.677`) | **40.1x faster load** vs cold (`8.94x` faster than `CGSNAP02`) |
| `Mathlib.Data.Real.Basic` `--backend cpu --jobs 16 --snapshot` | `Accepted` | `3,432.099` | `9,779.040` | **7.36x faster load** vs cold CPU; zero `.olean` re-parse |
| `Mathlib.Data.Real.Basic` `--backend hybrid --jobs 16 --verify-olean-hashes --snapshot` | `Accepted` (`98,965` GPU / `118,509` delegated) | `889.982` | `13,539.607` (`upload=131.301`, `kernel=12,820.706`, `readback=243.292`, `fallback=229.082`) | Full `.olean` byte re-hash before GPU launch |
| Full `Mathlib` (`775,326` decls) `--backend hybrid --jobs 16 --save-snapshot` | `Accepted` (`768,246` eligible, `205,317` GPU / `570,009` delegated) | `186,966.085` | `138,479.809` (`upload=1,896.103`, `kernel=122,510.641`, `readback=2,024.077`, `fallback=597.834`) | `e_nodes_words=435,186,742` (`vm_paged` 8-GiB WGSL path); saves `3,589.47 MiB` `CGSNAP03` |
| Full `Mathlib` `--backend hybrid --jobs 16 --snapshot` | `Accepted` (`205,755` GPU / `569,571` delegated) | `4,381.678` | `144,859.809` (`upload=1,316.990`, `kernel=140,537.656`, `readback=1,885.972`, `fallback=720.900`) | **42.7x faster load** vs cold (`12.7x` faster than `CGSNAP02`) |
| Full `Mathlib` `--backend cpu --jobs 16 --snapshot` | `Accepted` | `36,175.172` | `114,293.762` | `150.47 s` end-to-end on 16 CPU threads from `CGSNAP03` |
| Full `Mathlib` `--backend hybrid --jobs 16 --verify-olean-hashes --snapshot` | `Accepted` (`205,506` GPU / `569,820` delegated) | `24,662.448` | `155,935.741` (`upload=1,274.798`, `kernel=151,717.608`, `readback=2,025.384`, `fallback=454.888`) | Strict `.olean` byte re-hash + checksum verification |

```text
=== Mathlib.Data.Real.Basic (217474 decls) ===
con-gpu verify [ACCEPTED] on AMD Radeon RX 7900 XTX (backend=Vulkan) [cold + save-snapshot 501.05 MiB]
  decls=217474 prefix_skipped=0 eligible=214460 gpu_verified=93428 gpu_rejected=0 delegated=124046 host_verified_delegated=124046
  load=23457.291 ms pcie_upload=224.851 ms gpu_kernel=9102.619 ms gpu_readback=249.463 ms host_fallback=333.236 ms total_verify=11478.865 ms (steps_gpu=211372421, max_scratch_words=21137)
con-gpu verify [ACCEPTED] on AMD Radeon RX 7900 XTX (backend=Vulkan) [CGSNAP03 --snapshot]
  decls=217474 prefix_skipped=0 eligible=214460 gpu_verified=99395 gpu_rejected=0 delegated=118079 host_verified_delegated=118079
  load=584.337 ms pcie_upload=153.543 ms gpu_kernel=11645.472 ms gpu_readback=87.421 ms host_fallback=246.677 ms total_verify=12219.551 ms (steps_gpu=260393940, max_scratch_words=26305)
con-gpu verify [ACCEPTED] on CPU rayon (threads=16) [CGSNAP03 --snapshot]: decls=217474 prefix_skipped=0 load=3432.099 ms verify=9779.040 ms
con-gpu verify [ACCEPTED] on AMD Radeon RX 7900 XTX (backend=Vulkan) [CGSNAP03 --verify-olean-hashes --snapshot]
  decls=217474 prefix_skipped=0 eligible=214460 gpu_verified=98965 gpu_rejected=0 delegated=118509 host_verified_delegated=118509
  load=889.982 ms pcie_upload=131.301 ms gpu_kernel=12820.706 ms gpu_readback=243.292 ms host_fallback=229.082 ms total_verify=13539.607 ms (steps_gpu=256182944, max_scratch_words=26305)

=== Full Mathlib v4.35.0 (775326 decls) ===
con-gpu verify [ACCEPTED] on AMD Radeon RX 7900 XTX (backend=Vulkan) [cold + save-snapshot 3589.47 MiB]
  decls=775326 prefix_skipped=0 eligible=768246 gpu_verified=205317 gpu_rejected=0 delegated=570009 host_verified_delegated=570009
  load=186966.085 ms pcie_upload=1896.103 ms gpu_kernel=122510.641 ms gpu_readback=2024.077 ms host_fallback=597.834 ms total_verify=138479.809 ms (steps_gpu=1214750196, max_scratch_words=29234)
con-gpu verify [ACCEPTED] on AMD Radeon RX 7900 XTX (backend=Vulkan) [CGSNAP03 --snapshot]
  decls=775326 prefix_skipped=0 eligible=768246 gpu_verified=205755 gpu_rejected=0 delegated=569571 host_verified_delegated=569571
  load=4381.678 ms pcie_upload=1316.990 ms gpu_kernel=140537.656 ms gpu_readback=1885.972 ms host_fallback=720.900 ms total_verify=144859.809 ms (steps_gpu=1362226473, max_scratch_words=29234)
con-gpu verify [ACCEPTED] on CPU rayon (threads=16) [CGSNAP03 --snapshot]: decls=775326 prefix_skipped=0 load=36175.172 ms verify=114293.762 ms
con-gpu verify [ACCEPTED] on AMD Radeon RX 7900 XTX (backend=Vulkan) [CGSNAP03 --verify-olean-hashes --snapshot]
  decls=775326 prefix_skipped=0 eligible=768246 gpu_verified=205506 gpu_rejected=0 delegated=569820 host_verified_delegated=569820
  load=24662.448 ms pcie_upload=1274.798 ms gpu_kernel=151717.608 ms gpu_readback=2025.384 ms host_fallback=454.888 ms total_verify=155935.741 ms (steps_gpu=1327648171, max_scratch_words=29234)
```
