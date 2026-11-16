# AWS 96-vCPU / 128 GB Deployment Kit

Production deployment and orchestration scripts for running Lean 4 formalization builds on high-core-count, tight-memory AWS instances (`c7i.24xlarge`, `c7a.24xlarge`, `c6i.24xlarge`: **96 vCPUs / 128 GB RAM = 1.33 GB/core**) under Ubuntu 22.04/24.04 or Amazon Linux 2023.

## Why Stock Lean 4 / Lake OOMs at 96 vCPUs / 128 GB

| Bottleneck | Stock Lean v4.35.0 | Optimized Toolchain + `lean-zygote` + Lake + `con-gpu` |
| --- | --- | --- |
| **Per-worker import RAM** | 96 independent `lean` processes each allocate `privateConstantMap` + duplicate `publicConstantMap` + redundant extension vectors/passes (~2–3 GB RSS each -> >192 GB -> Linux OOM killer) | `finalizeImport` elides redundant `publicConstantMap` hashing/allocation, pointer-shares unchanged `ir`/`server` base extension states, and reuses a shared read-only `emptyImported` array for untouched extensions; `lean-zygote` preloads & `Runtime.markPersistent`s (`m_rc == 0`) once and shares physical pages via Linux `fork()` CoW (0 RC dirty faults!) |
| **Concurrency vs RAM** | Stock Lake spawns unrestricted subprocesses regardless of available RAM | Lake `-j <N>` & `--max-memory-mb auto` inspect `/proc/meminfo` (`MemAvailable`) + cgroup v2 (`memory.max`, `memory.current`) and bound spawns via `Std.Semaphore` without shrinking child `LEAN_NUM_THREADS` |
| **Lake scheduler contention** | `BuildStore` takes mutex locks (`modifyGet`) on every read; linear `2N` `Task.bind` chains | Lock-free `Ref.get` store reads (`StoreInsts.lean`) + balanced binary-tree `Job.mixArray`/`collectArray` |
| **Elaboration hotspots** | 0% `whnf` cache hits under binders (`hasFVar`); `defEqPerm`/`defEqTrans` wiped; O(N) `Grind.ParentSet` | Sound let-free open-term `WHNF` caching (`LocalContext.hasLetOrMVarDecl`), cross-call `Meta` DefEq cache retention, hybrid small-list / `Std.HashSet`-backed `Grind.ParentSet` |
| **SAT & external checking** | Stock single-core checking & `LRAT.trim` | Optional `bv_decide` `con-gpu trim-check-lrat` hook (`Cert.lean`) + incremental queued `con-gpu daemon` (`--verify-con-gpu[=gpu\|cpu]`, GPU Vulkan or CPU-only AWS nodes) |

## Quickstart

### 1. Provision & Build on AWS (Ubuntu / AL2023)

```bash
chmod +x aws-deploy/deploy_aws_96vcpu.sh aws-deploy/lake_fast_build.sh
./aws-deploy/deploy_aws_96vcpu.sh --apply-sysctl --build-con-gpu
export PATH="/opt/lean-opt/bin:$PATH"
```

What `deploy_aws_96vcpu.sh` sets up automatically:
- **Stage 1 -> Self-Hosted Stage 2**: Clones `mimalloc v3.4.5`, builds Stage 1, runs `copy-leancpp` and builds self-hosted Stage 2 (`-DSTAGE=2`), and installs `lean-zygote` + `lean-zygote-client`. Pass `--skip-stage2` for a faster Stage 1-only install.
- **Native `cadical` & Rust `con-gpu`**: Checks `ldd` on `cadical` and builds native `cadical` (`cadical.mk`) if `libc++.so.1` is absent; when `--build-con-gpu` is set, bootstraps minimal `rustup` if `cargo` is missing and builds `con-gpu`. Pass `--skip-con-gpu` if Rust/Cargo is not needed on the host.
- **Prefix overrides**: Use `--install-dir <dir>` (default `/opt/lean-opt`) and `--build-dir <dir>` (default `/opt/lean-opt-build`).

### 2. Run a Fast Build with Multi-Snapshot CoW + `--fork-any`

```bash
# Prebuild your project's common base module, then build all dependents via CoW fork() across 96 vCPUs:
# Add --module when targeting Lean 4 module-system projects (such as mathlib4 v4.35.0+).
# Repeatable --profile preloads multiple CoW snapshots (e.g. mixed non-module + module:<Mod>);
# --fork-any is enabled by default so unmatched shaken-import modules fork from the clean-runtime CoW helper.
./aws-deploy/lake_fast_build.sh \
  --project /path/to/your/lean-project \
  --prebuild YourProj.Base \
  --profile Init \
  --profile module:YourProj.Base \
  --fork-any \
  --jobs 96 \
  --max-memory-mb auto
```

`lake_fast_build.sh` defaults `LEAN_NUM_THREADS` to `2` when `--jobs >= 32` (`4` otherwise) and `--fork-any` to enabled (`--no-fork-any` disables the clean-runtime CoW helper), strips `*/.elan/bin` from `PATH` and unsets `ELAN_TOOLCHAIN` so `lean-toolchain` shims never hijack the optimized binaries, and falls back through `/home/devin/build-lean4-s2/bin`, `/opt/lean-opt/bin`, and `/home/devin/build-lean4-s1/bin` (override with `--bin-dir` or `LEAN_BIN_DIR`). On exit, `lean-zygote` prints `snapshot_hits`, `clean_cow_hits`, and `fallbacks` counts.

### 3. Fast CoW Build + Incremental `con-gpu` Daemon Verification

```bash
# CPU-SIMD mode on GPU-less AWS compute nodes (or omit '=cpu' / use '--verify-con-gpu' with Vulkan GPU):
./aws-deploy/lake_fast_build.sh \
  --project /path/to/your/lean-project \
  --prebuild YourProj.Base \
  --import YourProj.Base \
  --con-gpu-base-olean YourProj.Base \
  --verify-con-gpu=cpu \
  --jobs 96 \
  --max-memory-mb auto
```

This starts a persistent `con-gpu daemon`, exports `CON_GPU_DAEMON_ADDR`, `CON_GPU_BATCH_QUEUE=1`, `LEAN_BV_DECIDE_CON_GPU=1`, and `LAKE_VERIFY_TRUST_BV_AX=1`, accelerates `bv_decide` binary LRAT trimming/checking in `Cert.lean`, queues emitted `.olean`s cleanly, flushes the merged batch (`con-gpu verify --daemon-addr ... --flush`) after `lake build`, and sends `SHUTDOWN` cleanly on exit.

### 4. Cold-Build Mode (Heterogeneous DAG without CoW Daemon)

```bash
./aws-deploy/lake_fast_build.sh \
  --project /path/to/your/lean-project \
  --no-zygote \
  --jobs 96 \
  --max-memory-mb auto
```

## AWS 96-vCPU Benchmarks (`c7a.24xlarge`, `mathlib4 v4.35.0`)

Measured on an ephemeral AWS EC2 `c7a.24xlarge` (`AMD EPYC 9R14`, 96 physical cores, 184 GiB RAM, Ubuntu 24.04, `Linux 7.0.0-1014-aws`) using `benchmarks/measure_linux_bench.py`. Raw logs, JSON summaries, and built `.olean` archives are stored under `benchmarks/aws_mathlib4_v4.35.0/` and `benchmarks/mathlib4_real_basic_oleans/`.

| Benchmark | Configuration | Wall Time | Peak Concurrent Workers | Peak Agg RSS (MB) | Peak Agg PSS (MB) | Peak Agg Private (MB) | Kernel Verification |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Cold `Mathlib.Data.Real.Basic` (818 jobs) | Stock `v4.35.0` | 66.798s | 28 | 17144.82 | 4111.90 | 3545.12 | — |
| Cold `Mathlib.Data.Real.Basic` (818 jobs) | Stage 2 (`-j 96 --max-memory-mb auto`, `LEAN_NUM_THREADS=2`) | 70.352s | 27 | 16229.62 | 3504.56 | 3023.52 | Stock `leanchecker --fresh` exit 0; `con-gpu` (`cpu`, 96t) ACCEPTED (`217488` decls, `975.050 ms` verify) |
| Cold `Mathlib.Data.Real.Basic` (818 jobs) | Stage 2 (`-j 96 --max-memory-mb auto`, default threads) | 70.876s | 27 | 15039.36 | 3452.81 | 2642.71 | — |
| Cold `Mathlib.Data.Real.Basic` (818 jobs) | Stage 2 + `--module` CoW Zygote (`--prebuild Mathlib.Init`) | 76.126s | 34 | 18643.25 | 3771.83 | 3295.47 | — |
| Downstream `DownstreamReal` (96 modules importing `Mathlib.Basic.Real.Basic`, 908 jobs) | Stock `v4.35.0` | 5.325s | 18 | 15876.09 | 3222.00 | 2539.17 | — |
| Downstream `DownstreamReal` (96 modules) | Stage 2 (`-j 96 --max-memory-mb auto`) | 5.040s | 26 | 20320.05 | 3261.76 | 2410.80 | — |
| Downstream `DownstreamReal` (96 modules) | Stage 2 + `--module` CoW Zygote (`--import Mathlib.Basic.Real.Basic`, 96/96 CoW hits) | 6.105s (incl. cold daemon preload) | 23 | 2829.10 (-82.2%) | 1685.85 (-47.7%) | 1189.62 (-53.1%) | Stock `leanchecker --fresh` exit 0; `con-gpu` (`cpu`, 96t) ACCEPTED (`217680` decls, `966.309 ms` verify) |
| Cold Full `Mathlib` (9,053 jobs, 9,033 `.olean`s) | Stage 2 (`-j 96 --max-memory-mb auto`, `LEAN_NUM_THREADS=2`) | 606.244s (10m 06s) | 53 | 68166.79 | 13386.44 (13.07 GiB) | 12136.82 (11.85 GiB) | Stock `leanchecker --fresh Mathlib` exit 0; `con-gpu` (`cpu`, 96t) ACCEPTED (`775340` decls, `11284.458 ms` verify) |

Note: Cold upstream `Mathlib` uses shaken per-module imports (`100%` `module` mode across 8,624 `Mathlib/**/*.lean` files, top exact tuple `('Mathlib.Init',)` = 134 files), so `--no-zygote` / direct `lake build -j 96 --max-memory-mb auto` avoids prebuild barrier overhead while Stage 2 cuts aggregate PSS/private RAM by 15–25%. Downstream formalization crates sharing a common umbrella import (`module` + `public import ...`) achieve 100% CoW snapshot hits and cut aggregate RSS by 5.61x (`15.88 GB -> 2.83 GB`) and private dirty RAM by >53%.

### Phase 4 AWS 96-vCPU Benchmarks (`c7a.24xlarge`, `mathlib4 v4.35.0`)

Re-measured after Phase 4 Lean 4 / Lake / `lean-zygote` (process-isolated multi-profile CoW + `--fork-any`) / `con-gpu` (`CGSNAP03`) updates on an ephemeral `c7a.24xlarge` (`AMD EPYC 9R14`, 96 physical cores, 184 GiB RAM, Ubuntu 24.04, `Linux 7.0.0-1014-aws`, git hash `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). Artifacts and SHA256 manifest live in `benchmarks/aws_mathlib4_v4.35.0_phase4/`.

| Benchmark | Configuration | Wall Time | Peak Workers | Peak Agg RSS (MB) | Peak Agg PSS (MB) | Peak Agg Private (MB) | Notes / Verification |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Mathlib.Data.Real.Basic` (818 jobs) | Stock `v4.35.0` Cold | 65.463s | 28 | 15832.95 | 3796.70 | 3247.56 | Baseline (`797` `.olean`s) |
| `Mathlib.Data.Real.Basic` (818 jobs) | Phase 4 Stage 2 Cold (`-j 96 --max-memory-mb auto`, `LEAN_NUM_THREADS=2`) | 71.320s | 23 | 13901.92 (-12.2%) | 3177.81 (-16.3%) | 2371.61 (-27.0%) | `775/797` SHA256 exact match vs Stock (`22` differ in v3 closure relocation tables) |
| `Mathlib.Data.Real.Basic` (818 jobs) | Phase 4 Stage 2 + Multi-Profile `--fork-any` Zygote (`--prebuild Mathlib.Init`, `--profile module:Init --profile module:Mathlib.Init --fork-any`) | 82.529s (incl. prebuild + 2 isolated snapshots) | 54 | 14472.32 | 2960.19 (-22.0%) | 2472.15 | `snapshot_hits=40`, `clean_cow_hits=667`, `fallbacks=0`; **`797/797` exact `.olean` SHA256 match** vs Phase 4 Cold |
| `DownstreamReal` (96 modules `public import Mathlib.Data.Real.Basic`) | Stock `v4.35.0` Cold | 93.998s | 29 | 24436.88 | 4492.60 | 3369.39 | Cold multi-package build |
| `DownstreamReal` (96 modules) | Phase 4 Stage 2 + `--module` Zygote (`--profile module:Mathlib.Data.Real.Basic --fork-any`) | **6.592s (14.26x faster)** | 23 | **2823.56 (-88.4%)** | **1718.99 (-61.7%)** | **1221.98 (-63.7%)** | `snapshot_hits=96`, `clean_cow_hits=1`, `fallbacks=0` |
| Full `Mathlib` (9,053 jobs, `9,033` `.olean`s) | Phase 4 Stage 2 Cold (`-j 96 --max-memory-mb auto`, `LEAN_NUM_THREADS=2`) | **602.782s (10m 03s)** | 49 | 63060.64 | 13726.32 (13.40 GiB) | 12566.23 (12.27 GiB) | Zero OOMs across all 96 cores |
| Full `Mathlib` (9,046 jobs, `9,033` `.olean`s) | Phase 4 Stage 2 + `--fork-any` CoW Zygote (`--profile module:Init --fork-any`, Mathlib `.olean`s cleaned) | 620.804s | 102 | 62269.42 | **11272.67 (11.01 GiB, -17.9%)** | **10049.27 (9.81 GiB, -20.0%)** | `snapshot_hits=1`, `clean_cow_hits=8624`, `fallbacks=0` |
| Full `Mathlib` Verify | Stock `v4.35.0` `leanchecker --fresh Mathlib` | 1480.583s (24m 41s) | — | 8746.60 | 8744.29 | 8744.14 | `exit_code=0` on Phase 4 built `.olean`s |
| Full `Mathlib` Verify | Phase 4 `con-gpu verify ... --fresh --backend cpu --jobs 96 --save-snapshot` | 126.860s (**11.67x faster**) | — | 18230.30 | 18228.16 | 18228.03 | `[ACCEPTED]`, `775,357` decls (`load=102433.196 ms`, `verify=10607.149 ms`), `3.6G` `CGSNAP03` (`435,195,527` e-node words) |
| Full `Mathlib` Verify | Phase 4 `con-gpu verify ... --fresh --backend cpu --jobs 96 --snapshot` (`CGSNAP03`) | **33.670s (43.97x faster)** | — | 7412.96 | 7410.93 | 7410.81 | `[ACCEPTED]`, `775,357` decls (`load=21459.593 ms`, **`verify=11679.454 ms`**) |

## Key Environment Variables

- `LEAN_ZYGOTE_SOCK`: Unix domain socket path for `lean-zygote` / `lean-zygote-client`.
- `LEAN_ZYGOTE_DISABLE=1`: Force `lean-zygote-client` to bypass the daemon and exec `$LEAN_BIN`.
- `LAKE_LEAN_WRAPPER`: Compiler wrapper path (automatically set by `--zygote`).
- `LAKE_MAX_MEMORY_MB`: RAM budget in MB or `auto` (`--max-memory-mb`).
- `LAKE_WORKER_MEM_MB`: Override estimated per-worker RAM footprint (defaults: `384` MB with `--zygote`, `2048` MB cold).
- `LAKE_EXTERNAL_VERIFIER`: External `.olean` checker binary (`--verify-with-con-gpu`, auto-resolved to `con-gpu` / `con-gpu.exe`).
- `CON_GPU_BIN`: Explicit path override for `con-gpu` binary.
- `CON_GPU_DAEMON_ADDR`: Persistent `con-gpu daemon` TCP address (e.g., `127.0.0.1:47831`).
- `CON_GPU_BATCH_QUEUE`: Set to `1` so Lake sends `--queue` per module and flushes cleanly at end of build.
- `CON_GPU_BACKEND`: Optional backend override (`gpu` | `cpu` | `hybrid`) propagated to `con-gpu` hooks.
- `LEAN_BV_DECIDE_CON_GPU`: Set to `1` (or explicit `con-gpu` path) to enable `con-gpu trim-check-lrat` inside `bv_decide`.
- `LAKE_VERIFY_TRUST_BV_AX`: Set to `1` to pass `--trust-bv-decide-axioms` from Lake to `con-gpu`.
- `LAKE_VERIFY_STRICT`: Set to `1` to treat `con-gpu` `DECLINED` (`exit 2`) as a hard build failure instead of a warning.
