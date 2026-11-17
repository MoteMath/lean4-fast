# Independent Verification & Benchmark Report

**Role:** Independent Soundness, Provenance & Performance Verifier (`@verifier`)  
**Scope:** End-to-end Phase 2 (Wave H), Phase 3 (Wave L), Phase 4 (Wave Q), and Phase 5 (Wave U2) independent verification of `ConGpuProof`, `con-gpu` (CPU `rayon` + Vulkan RX 7900 XTX / NVIDIA L40S / NVIDIA A10G), Stage 2 `lean4`, multi-profile `lean-zygote`, and the 13-closure / 14-suite AWS & local ecosystem benchmark ([ECOSYSTEM_BENCHMARK_REPORT.md](file:///c:/Users/devin/Desktop/lean/benchmarks/ECOSYSTEM_BENCHMARK_REPORT.md)).  
**Suite:** [downstream_bench](file:///c:/Users/devin/Desktop/lean/benchmarks/downstream_bench/lakefile.toml) (`32` modules + root `DownstreamBench` = `33` `.lean` files, plus `9` adversarial fixtures in [adversarial](file:///c:/Users/devin/Desktop/lean/benchmarks/downstream_bench/adversarial)) and Phase 5 `aws_ecosystem_phase5` (`4` platforms, `13` closures, `14` build suites)  
**Overall Verdict:** **PASS** across Phases 2–5: Phase 4 Gate 1 (`58/58` theorems in `ConGpuProof`), Gate 2 (`38/38` Cargo tests + Full `mathlib4` RX 7900 XTX), Gate 3 (WSL2 Stage 2 + Multi-Profile Zygote + stock `leanchecker`), Gate 4 (`35/35` AWS Phase 4 artifacts), and Phase 5 Wave U2 (`356/356` SHA256 checksums across `4` artifact sets, `13/13` stock `leanchecker` `exit=0`, `13/13` multi-platform `con-gpu` decl/verdict parity, `4/4` `test-soundness` & `7/7` `bench-synthetic` runs, `vendor/con-ron` & AWS cleanup verified, Rule 2 clean).

---

## 1. Environment, Baselines & AWS Billing Hygiene

- **Windows 11 Host:** AMD Ryzen 7 3700X (`16` logical CPUs), `32 GiB` RAM, AMD Radeon RX 7900 XTX (`backend=Vulkan, max_storage=2147483644`).
- **WSL2 Ubuntu Linux (`ext4`, `ulimit -c 0`):** Self-hosted Stage 2 toolchain at `/home/devin/build-lean4-s2/bin/{lean,lake,leanir,leanc,leanchecker,lean-zygote,lean-zygote-client}` (`37` changed files, `+2032 / -453` in `lean4/`).
- **Stock Toolchain:** Lean `v4.35.0` (`commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake `5.0.0-src+eb6cafb`).
- **Pre-Wave Stock Baselines ([BASELINE.md](file:///c:/Users/devin/Desktop/lean/benchmarks/BASELINE.md)):**
  - WSL2 Linux uncapped `lake build` (`DownstreamBench`, `35` jobs, `15` peak workers, [baseline_stock_linux.json](file:///c:/Users/devin/Desktop/lean/benchmarks/baseline_stock_linux.json)): **`9.714 s`**, `10,814.17 MB` agg RSS, `1,607.92 MB` agg PSS, `884.85 MB` agg private.
  - Windows 11 `lake.exe build --wfail` (`35` jobs): **`22.586 s`**.
  - Windows 11 stock `leanchecker.exe`: `DownstreamBench` (`27.477 s` replay), `Init` (`49.011 s` replay; `--fresh Init` `150.365 s`), `Std` (`84.019 s` replay).
- **AWS Billing Hygiene Audit (`us-east-1`, Wave H):**
  - `aws.exe ec2 describe-instances --region us-east-1 --instance-ids i-048eebe9f73da797f`: `c7a.24xlarge` (`Name=lean4-96vcpu-mathlib-bench`) confirmed **`terminated`** (`2026-11-15T15:17:46+00:00`).
  - Region-wide `describe-instances`: **`0`** `lean4-*` EC2 instances `running` or `pending` (only pre-existing `r6a.8xlarge` `stopped` and `mathregistry-builder-ondemand*` instances).

---

## 2. Gate 1 — Lean 4 Formal Proof Audit ([con-gpu/proof](file:///c:/Users/devin/Desktop/lean/con-gpu/proof))

- **Toolchain & Source Scope:** `leanprover/lean4:v4.35.0` across all `7` `.lean` files (`ConGpuProof.lean`, `ConGpuProof/{ArenaOps,ArenaSpec,AxiomAudit,LratParallel,Reductions,StepMachine}.lean`).
- **Comment-Stripped Forbidden-Construct Scan:** Scanned non-comment lines for `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `implemented_by`, `extern`, `native_decide`, `bv_decide`, `sorryAx`, and `LC.c`: **`FILES_SCANNED=7 FORBIDDEN_NON_COMMENT_HITS=0`** (`SCAN_RC=0`).
- **Clean Build & Kernel Audit:**
  - `lake.exe clean`: `exit=0` (`0.248 s`).
  - `lake.exe build --wfail`: **`exit=0`** (`21.835 s`, `8` jobs, `0` warnings aside from expected `#print axioms` `info:` output).
  - `lake.exe env lean ConGpuProof/AxiomAudit.lean`: **`exit=0`** (`1.202 s`); all **`29`** theorems in [AxiomAudit.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/AxiomAudit.lean#L14-L42) depend exclusively on standard Lean axioms (`24` use `[propext, Classical.choice, Quot.sound]`, `4` use `[propext, Quot.sound]`, `1` (`indexedIota_sound`) uses `[propext]`, `0` custom axioms / `sorryAx`).
  - Stock `leanchecker.exe --fresh ConGpuProof.AxiomAudit`: **`exit=0`** (`82.799 s`).

**Gate 1 Verdict:** **PASS**

---

## 3. Gate 2 — `con-gpu` RX 7900 XTX & CPU-SIMD Soundness + Throughput

- **Static Arithmetic & Binary Audit ([con-gpu/crates](file:///c:/Users/devin/Desktop/lean/con-gpu/crates)):**
  - Scanned `18` Rust files and `9` WGSL shaders (comment-stripped): **`FP_CODE_HITS=0`** (`f16`/`f32`/`f64`/`float`/`from_bits`/`to_bits`), **`WGSL_INT64_CODE_HITS=0`** (`u64`/`i64`/`SHADER_INT64`).
  - [con-gpu/Cargo.toml](file:///c:/Users/devin/Desktop/lean/con-gpu/Cargo.toml) `[profile.release]` uses `opt-level = 3, lto = false, codegen-units = 16, overflow-checks = true`, and all `5` workspace `Cargo.toml` manifests have `0` floating-point crate dependencies.
  - Release binary `target/release/con-gpu.exe`: `10,869,248` bytes.
  - [con-gpu/README.md](file:///c:/Users/devin/Desktop/lean/con-gpu/README.md): `GEMINI.md` Rule 2 math check passed (`banned=0, unpadded_inline_underscore=0`).
- **Workspace Test Suite (`cargo test --workspace --release -- --test-threads=1 --nocapture`, `exit=0`, `65.822 s`):**
  - **`34 passed; 0 failed; 0 ignored`** across `5` test binaries (`0` doc-tests across crates):
    - `con_gpu_arena` (`src/lib.rs`): `15 passed; 0 failed` (`2.93 s`)
    - `con_gpu_arena` (`tests/init_smoke.rs`): `3 passed; 0 failed` (`24.21 s`; `Init` lazy `load_ms=3617, host_ms=11441, threads=16`; `Init` materialized `decls=63937, thm_mat=45494, eligible=63308, load_ms=3313, mat_ms=4862, pack_ms=554, e_nodes_words=25486086`)
    - `con-gpu` (`src/main.rs`): `5 passed; 0 failed` (`4.59 s`)
    - `con_gpu_lrat` (`src/lib.rs`): `6 passed; 0 failed` (`0.40 s`; `100K` LRAT RX 7900 XTX `steps=25001, gpu_kernel_us=1265, upload_us=870`)
    - `con_gpu_shaders` (`src/lib.rs`): `5 passed; 0 failed` (`32.60 s`; `gpu_typecheck_init_hybrid_differential` RX 7900 XTX `total=63937, eligible=63308, gpu_verified=20259, gpu_rejected=0, delegated=43678, pcie_upload_ms=60, gpu_kernel_ms=1604, max_quantum_ms=57, gpu_readback_ms=13, host_fallback_ms=3973, steps_gpu=40681593, max_scratch_words=20017`; `E2E` `tested=11, gpu_verified_sum=326, gpu_rejected_sum=2`)
- **Sequential Differential Soundness Suite (`con-gpu.exe test-soundness`, `exit=0`, `369.463 s`):**
  - `Pipeline B bignum_nat exact batch tests: 40/40 ops matched`
  - `Pipeline C LRAT fixtures (GPU & CPU differential): 3 accepted, 7 rejected`
  - `Corrupt .olean files rejected: 4/4`
  - `Pipeline A con-leche differential soundness: tested=587 accepted=341 rejected=246 gpu_verified=21132 gpu_rejected=127 delegated=10208` *(per [main.rs](file:///c:/Users/devin/Desktop/lean/con-gpu/crates/con-gpu-cli/src/main.rs#L1678-L1685), intentionally skips non-default `nat_size_limit` flag tests and `code == 124` infinite-loop fixtures).*

### Gate 2 Throughput (`con-gpu.exe bench --threads 16 --skip-leanchecker`, `exit=0`, `186.099 s`)

| Target / Mode | Coverage / Telemetry | `16T` CPU Rayon (ms) | RX 7900 XTX GPU Hybrid (ms) | GPU Kernel / Load Highlights |
| :--- | :--- | ---: | ---: | :--- |
| **`Init`** (`63,937` decls) | `Accepted`, `20,259` GPU / `43,678` deleg. | `5,573.963` | `6,410.625` | `load=10200.502`, `pack=760.270`, `upload=160.283`, **`kernel=1301.535`**, `fallback=4943.164` |
| **`Std`** (`109,213` decls) | `Accepted`, `28,659` GPU / `80,554` deleg. | `7,905.605` | `7,948.013` | `load=17353.216`, `pack=1018.181`, `upload=112.850`, **`kernel=1912.507`**, `fallback=5901.546` |
| **`DownstreamBench` (strict)** (`114,770` decls) | `Declined@114126` (`bv_decide` axiom) | `8,225.575` | `8,564.668` | `29,221` GPU / `85,549` deleg., `kernel=2017.250`, `fallback=6366.029` |
| **`DownstreamBench` (`--trust-bv-decide-axioms`)** | `Accepted`, `29,221` GPU / `85,549` deleg. | `8,895.271` | **`8,288.868`** | `load=17195.110`, `pack=1133.597`, **`kernel=1803.311`**, `fallback=6327.017` |
| **`100K` Synthetic LRAT** (`25,001` steps) | `verified=25001`, `delegated=0` | `52.381` | **`3.092`** (**`16.9x`**) | `pcie_upload=1.239`, **`gpu_kernel=0.785`** |
| **Pipeline B `BignumNat`** (`16,384` ops) | Exact `u32` limb batch | — | — | **`gpu_kernel=0.440`** |
| **Incremental `Init.Prelude -> Init`** | `prefix_skipped=2002`, `delta=61935` | — | `5,021.260` (`inc_verify`) | `inc_load=9824.620`, `inc_pack=609.174`, `kernel=2098.544`, `e2e=15455.055`, `fs_hits=4538/1959` |
| **Snapshot `--snapshot Init`** | `size_mib=105.71`, `decls=63937` | — | `13,075.437` (`snap_verify`) | `save=156.218`, `prefetch_hash=346.008`, **`snap_load=151.590`**, **`kernel=833.394`**, `fallback=12189.981`, `e2e=13573.036` |
| **Incremental `Std -> DownstreamBench`** | `prefix_skipped=3980`, `delta=110790` | — | `7,891.823` (`inc_verify`) | `inc_load=14680.736`, `inc_pack=850.188`, `kernel=2379.945`, `e2e=23422.749`, `fs_hits=17977/3474` |

### `Mathlib.Data.Real.Basic` Verification (`--fresh`, `--jobs 16`, `--trust-bv-decide-axioms`)

Verified locally from the unpacked AWS archive (`benchmarks/mathlib4_real_basic_oleans/unpacked/` combined with Windows stock `v4.35.0` `Init`/`Std` `.olean`s -> `decls=217,474`), then deleted `unpacked/` while preserving [mathlib4_real_basic_oleans.tar.zst](file:///c:/Users/devin/Desktop/lean/benchmarks/mathlib4_real_basic_oleans/mathlib4_real_basic_oleans.tar.zst):

- **Cold RX 7900 XTX Hybrid (`--fresh --backend hybrid --jobs 16`):** **`exit=0`** (`33.948 s` wall), `[ACCEPTED]`, `decls=217474 prefix_skipped=0 eligible=214462 gpu_verified=74984 gpu_rejected=0 delegated=142490 host_verified_delegated=142490`, `load=22564.386 ms pcie_upload=112.609 ms gpu_kernel=4396.880 ms gpu_readback=163.477 ms host_fallback=4782.923 ms total_verify=10653.158 ms`, `steps_gpu=78816944 max_scratch_words=21137`.
- **`--save-snapshot`:** **`exit=0`** (`33.788 s` wall), `262,021,516` bytes (`249.88 MiB`, `jobs=217474, e_nodes_words=57150658`), `load=21914.006 ms`, `gpu_kernel=4675.319 ms`, `total_verify=10713.294 ms`.
- **`--snapshot` (`--fresh --backend hybrid --jobs 16`):** **`exit=0`** (`39.279 s` wall), `[ACCEPTED]`, `load=2109.595 ms` (`10.7x` faster arena load), `pcie_upload=121.877 ms`, **`gpu_kernel=1868.445 ms`**, `gpu_readback=6.163 ms`, `host_fallback=34210.026 ms` *(snapshot lazy loader skips upfront full `.olean` loading, so host `.olean` reads for the `142,490` delegated decls occur inside `host_fallback`)*, `total_verify=36308.036 ms`.
- **Exact CPU Rayon (`--fresh --backend cpu --jobs 16`):** **`exit=0`** (`36.981 s` wall), `[ACCEPTED]`, `decls=217474 load=25684.830 ms verify=10651.339 ms`.

**Gate 2 Verdict:** **PASS**

---

## 4. Gate 3 — Self-Hosted Stage 2 Runtime, Lake, `lean-zygote` & Stock Provenance (Wave H)

- **Code, Script & Toolchain Checks:**
  - `aws-deploy` scripts ([deploy_aws_96vcpu.sh](file:///c:/Users/devin/Desktop/lean/aws-deploy/deploy_aws_96vcpu.sh), [lake_fast_build.sh](file:///c:/Users/devin/Desktop/lean/aws-deploy/lake_fast_build.sh)): `CRLF=0`, `bash -n` `exit=0`; [aws-deploy/README.md](file:///c:/Users/devin/Desktop/lean/aws-deploy/README.md) passes `GEMINI.md` Rule 2 (`banned=0, unpadded_inline_underscore=0`).
  - Stage 2 binaries verified under `/home/devin/build-lean4-s2/bin/`: `lean` (`v4.35.0`), `lake` (`5.0.0-src+eb6cafb`), `leanir`, `leanc` (`cc 13.3.0`), `leanchecker`, `lean-zygote`, `lean-zygote-client`.
  - [rc_model.lean](file:///c:/Users/devin/Desktop/lean/lean4/tests/elab/rc_model.lean): `0` `sorry`/`admit` hits; compiles cleanly with Stage 2 `lean` (**`exit=0`**, `20.939 s`, `3` `mvcgen` deprecation warnings).
  - Stage 2 adversarial suite ([adversarial](file:///c:/Users/devin/Desktop/lean/benchmarks/downstream_bench/adversarial)): **`9/9`** rejected or flagged (`exit=0`).
  - Stage 2 Lake regression suite (`lean4/tests/lake/tests`): **`6/6` PASSED** (`emptyBuild`, `needs`, `failFast`, `lean`, `buildArgs`, `noBuild`, `exit=0`).
- **End-to-End `Cert.lean` GPU Hook, Stage 2 `lake --verify-with-con-gpu -j 16`, & `lake_fast_build.sh`:**
  - Compiled `DownstreamBench/BV/StateMachineSafety.lean` via Stage 2 `lean` with `LEAN_BV_DECIDE_CON_GPU` (`CON_GPU_BACKEND=gpu`): **`exit=0`** (`1.468 s`), all `5/5` theorems emitted `con-gpu trim-check-lrat verified and trimmed LRAT certificate`.
  - Clean `33`-module Stage 2 `lake build --wfail -j 16 --max-memory-mb auto --verify-with-con-gpu` (`CON_GPU_DAEMON_ADDR=127.0.0.1:47831`, `CON_GPU_BATCH_QUEUE=1`, `LEAN_BV_DECIDE_CON_GPU=1`, `LAKE_VERIFY_TRUST_BV_AX=1`): **`exit=0`** (`12.536 s`, `35` jobs, `33` `.olean`s). Flushed on Windows via `con-gpu.exe verify --daemon-addr 127.0.0.1:47831 --flush --trust-bv-decide-axioms`: **`exit=0`** (`23.7 s` client wall, `elapsed_us=9389271`, `ACCEPTED flushed=33 batches=1 total=114770 prefix_skipped=0 eligible=113638 gpu_verified=29221 delegated=85549 host_verified=85549 gpu_kernel_us=2175097 pcie_upload_us=113472`). Daemon `STATS requests=71 verified_decls=114770 rejected_decls=0 base_cached=false queued=0`; `SHUTDOWN` -> `BYE`, daemon exited `0`.
  - `aws-deploy/lake_fast_build.sh` `-j 16 --max-memory-mb auto` on `DownstreamBench.Algebra.MonoidLaws`:
    - `--verify-con-gpu=gpu`: **`exit=0`** (`31.384 s`), `MonoidLaws` built in `167 ms`, flushed `ACCEPTED flushed=1 batches=1 total=113517 eligible=112441 gpu_verified=28962 delegated=84555 host_verified=84555 gpu_kernel_us=1958501 pcie_upload_us=111562 elapsed_us=9139666`, `STATS requests=2 verified_decls=113517 rejected_decls=0`.
    - `--verify-con-gpu=cpu`: **`exit=0`** (`24.019 s`), `MonoidLaws` built in `169 ms`, flushed `ACCEPTED flushed=1 batches=1 total=113517 ... elapsed_us=7195208` *(CPU-only daemon mode reports `0` for GPU telemetry counters)*, `STATS requests=2 verified_decls=113517 rejected_decls=0`.
- **`16`-Worker (`-j 16`, Wave H) & `4`-Worker (Wave 3) Linux `smaps_rollup` Profiles (`DownstreamBench`, `33` `.olean`s):**

| Configuration | Exit / Jobs | Elapsed (s) | Speedup vs Baseline | Peak Agg RSS (MB) | Peak Agg PSS (MB) | Peak Agg Private (MB) | Median Worker PSS / Priv (MB) |
| :--- | :--- | ---: | :--- | ---: | ---: | ---: | ---: |
| **Stock `v4.35.0` uncapped (`15` peak workers)** ([baseline_stock_linux.json](file:///c:/Users/devin/Desktop/lean/benchmarks/baseline_stock_linux.json)) | `0` / `35` | `9.714` | `1.00x` (`15w`) | `10,814.17` | `1,607.92` | `884.85` | `181.33` / `79.25` |
| **Stage 2 Cold `-j 16 --max-memory-mb auto`** (Wave H, `11` peak workers) | `0` / `35` | **`8.622`** | **`1.13x`** (`vs 15w`) | `8,103.42` | `1,490.55` | `732.88` | `213.71` / `67.80` |
| **Stage 2 `lake_fast_build.sh --zygote -j 16`** (Wave H, E2E incl. Prelude+daemon) | `0` / `35` | **`7.423`** | **`1.31x`** (`vs 15w`) | `6,865.62` | **`1,382.21`** | `784.59` | **`84.06`** / **`52.23`** |
| **Stock `4w` warm cache** ([stock_4w_warm.json](file:///c:/Users/devin/Desktop/lean/benchmarks/stock_4w_warm.json); cold [stock_4w.json](file:///c:/Users/devin/Desktop/lean/benchmarks/stock_4w.json): `14.250 s`) | `0` / `35` | `10.322` | `1.00x` (`4w`) | `2,913.34` | `1,169.46` | `695.05` | `340.19` / `93.99` |
| **Stage 1 Cold `-j 4 --max-memory-mb auto`** ([opt_cold_4w.json](file:///c:/Users/devin/Desktop/lean/benchmarks/opt_cold_4w.json)) | `0` / `35` | `8.328` | `1.24x` (`vs 4w`) | `2,999.64` | `1,070.08` | `678.92` | `333.60` / `79.33` |
| **Stage 1 `lake_fast_build.sh --zygote -j 4`** ([opt_zygote_lfb_4w.json](file:///c:/Users/devin/Desktop/lean/benchmarks/opt_zygote_lfb_4w.json); Phase 3 [opt_zyg_phase3_4w.json](file:///c:/Users/devin/Desktop/lean/benchmarks/opt_zyg_phase3_4w.json): `5.134 s`) | `0` / `35` | `7.881` | `1.31x` (`vs 4w`) | `3,550.29` | `1,071.97` | `711.88` | `72.32` / `29.38` |

*(Note: In [measure_linux_bench.py](file:///c:/Users/devin/Desktop/lean/benchmarks/measure_linux_bench.py), `--zygote` worker counts include both thin `lean-zygote-client` shims and forked `lean-zygote` workers, while `Peak Agg RSS/PSS/Private` reflects true total simultaneous memory across the entire build tree plus daemon.)*

- **`100%` Stock `v4.35.0` `leanchecker.exe --fresh` Provenance (Wave H):**
  - Cross-tree byte check (`33` `.olean`s): all `25` non-BV modules were SHA256-identical between Stage 2 `--verify-with-con-gpu` (`LEAN_BV_DECIDE_CON_GPU=1`) and Stage 2 `lake_fast_build.sh --zygote -j 16`, differing only on the `8` `DownstreamBench/BV/*.olean` files whose trimmed LRAT certificates came from `con-gpu trim-check-lrat` vs built-in `LRAT.trim`.
  - Unmodified stock `C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanchecker.exe --fresh DownstreamBench` on Stage 2 `--verify-with-con-gpu` `.olean`s: **`exit=0`** (`134.965 s`).
  - Unmodified stock `leanchecker.exe --fresh DownstreamBench` on Stage 2 `lake_fast_build.sh --zygote -j 16` `.olean`s: **`exit=0`** (`126.067 s`).

**Gate 3 Verdict:** **PASS**

---

## 5. AWS `c7a.24xlarge` (`96`-vCPU) `mathlib4 v4.35.0` Artifact Audit

- **Host & Checksum Integrity:**
  - Verified against [sysinfo.txt](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/sysinfo.txt) (`AMD EPYC 9R14`, `96` physical cores, `184 GiB` RAM, Ubuntu 24.04, `Linux 7.0.0-1014-aws`).
  - Verified SHA256 digests of all `27` files in [local_sha256sums.txt](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/local_sha256sums.txt) against [remote_sha256sums.txt](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/remote_sha256sums.txt): **`LOCAL_SHA256_CHECKED=27 MISMATCHES=0`**. [mathlib4_real_basic_oleans.tar.zst](file:///c:/Users/devin/Desktop/lean/benchmarks/mathlib4_real_basic_oleans/mathlib4_real_basic_oleans.tar.zst) (`137,729,165` bytes) also matches remote SHA256 (`cfe3a3a9d428069178d5bcffef3c86dc060f7877b2c2ec6a755da5401f247ade`, `4,788` archive entries).
  - Verified [aws_mathlib4_v4.35.0_oleans.tar.zst](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/aws_mathlib4_v4.35.0_oleans.tar.zst) (`1,721,186,617` bytes) unpacks cleanly in streaming `zstd -dc | tar -tf -` with **`54,190`** entries covering the `9,033` `.olean` build tree *(an auxiliary trailing `tar` call at [finish_full_mathlib.log](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/finish_full_mathlib.log#L101-L102) printed `Argument list too long`, while the archived `.tar.zst` matches SHA256 `6d9cd34d7e015e4a5aee53b3daf47f2bbc1ed899c5692c62741b2625af35463f` and contains all `54,190` entries)*.
- **Audited AWS Benchmarks & Kernel Verification ([benchmarks/aws_mathlib4_v4.35.0](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0)):**

| Target / Scope | Configuration | Wall Time (s) | Peak Workers | Peak Agg RSS (MB) | Peak Agg PSS (MB) | Peak Agg Private (MB) | Verification Logged |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| **`Mathlib.Data.Real.Basic`** (`818` jobs) | Stock `v4.35.0` ([real_stock.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/real_stock.json)) | `66.798` | `28` | `17,144.82` | `4,111.90` | `3,545.12` | — |
| **`Mathlib.Data.Real.Basic`** (`818` jobs) | Stage 2 (`-j 96 --max-memory-mb auto`, `2T`) ([real_opt_s2.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/real_opt_s2.json)) | `70.352` | `27` | `16,229.62` | `3,504.56` | `3,023.52` | Stock `leanchecker` rc `0`; `con-gpu` CPU (`96t`) `217,488` decls, `975.050 ms` |
| **`Mathlib.Data.Real.Basic`** (`818` jobs) | Stage 2 (default threads) ([real_opt_s2_defaultthreads.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/real_opt_s2_defaultthreads.json)) | `70.876` | `27` | `15,039.36` | `3,452.81` | `2,642.71` | — |
| **`Mathlib.Data.Real.Basic`** (`818` jobs) | Stage 2 + Zygote (`--prebuild Mathlib.Init`) ([real_opt_zygote.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/real_opt_zygote.json)) | `76.126` | `34` | `18,643.25` | `3,771.83` | `3,295.47` | — |
| **`DownstreamReal`** (`96` mods, `908` jobs) | Stock `v4.35.0` ([downstream_real_stock.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/downstream_real_stock.json)) | `5.325` | `18` | `15,876.09` | `3,222.00` | `2,539.17` | — |
| **`DownstreamReal`** (`96` mods, `908` jobs) | Stage 2 (`-j 96 --max-memory-mb auto`) ([downstream_real_s2.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/downstream_real_s2.json)) | `5.040` | `26` | `20,320.05` | `3,261.76` | `2,410.80` | — |
| **`DownstreamReal`** (`96` mods, `908` jobs) | Stage 2 + Zygote (`--import Mathlib.Basic.Real.Basic`) ([downstream_real_zygote.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/downstream_real_zygote.json)) | `6.105` | `23` | **`2,829.10`** | **`1,685.85`** | **`1,189.62`** | Stock `leanchecker` rc `0`; `con-gpu` CPU (`96t`) `217,680` decls, `966.309 ms` |
| **Full `Mathlib`** (`9,053` jobs, `9,033` `.olean`s) | Stage 2 (`-j 96 --max-memory-mb auto`, `2T`) ([full_opt_mathlib.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/full_opt_mathlib.json)) | **`606.244`** | `53` | `68,166.79` | **`13,386.44`** | **`12,136.82`** | `FULL_STOCK_LEANCHECKER_RC=0`; `con-gpu` CPU (`96t`) **`775,340`** decls, `verify=11,284.458 ms`, rc `0` |

---

## 6. Workspace & Scratch Hygiene

- Removed `benchmarks/mathlib4_real_basic_oleans/unpacked/` after independent verification; preserved `mathlib4_real_basic_oleans.tar.zst`.
- Removed `/home/devin/wave_h_verify`, `/home/devin/wave_h_lake`, `$SCRATCH/wave_h_oleans*`, and all temporary scripts, snapshots, and JSON scratch outputs.
- Confirmed `CLEAN_WSL_DIR`, `CLEAN_WSL_PROCS`, `CLEAN_WSL_TMP`, and zero stray `con-gpu`/`lean`/`lake`/`leanchecker` processes on Windows.

---

## 7. Phase 3 (Waves I, J, K, K2, L) Independent Audit

### 7.1 Gate 1 — Lean 4 Formal Proof Audit ([con-gpu/proof](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof.lean))

- Audited `8` `.lean` files ([ConGpuProof.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof.lean), [ArenaSpec.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/ArenaSpec.lean), [ArenaOps.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/ArenaOps.lean), [StepMachine.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/StepMachine.lean), [LratParallel.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/LratParallel.lean), [Reductions.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/Reductions.lean), [Phase3Soundness.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/Phase3Soundness.lean), [AxiomAudit.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/AxiomAudit.lean)).
- Comment-stripped scan (`sorry|admit|axiom|unsafe|partial|implemented_by|extern|native_decide|bv_decide|sorryAx|LC.c`): `0` hits across all `8` files.
- `lake.exe clean` (`exit=0`), `lake.exe build --wfail` (`exit=0`, `0` warnings, `9` jobs), `lake.exe env lean ConGpuProof/AxiomAudit.lean` (`exit=0`): all `43` theorems in [AxiomAudit.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/AxiomAudit.lean) depend strictly on subsets of `{propext, Classical.choice, Quot.sound}`.
- Unmodified stock `C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanchecker.exe --fresh ConGpuProof.AxiomAudit`: `exit=0`.

### 7.2 Gate 2 — `con-gpu` Static Audit, Soundness & RX 7900 XTX Sequential Benchmarks

- **Static & release audit:** `18` `.rs` files under [con-gpu/crates](file:///c:/Users/devin/Desktop/lean/con-gpu/crates) -> `0` comment-stripped float/bitcast hits (`f16|f32|f64|float|from_bits|to_bits`); `9` `.wgsl` shader files -> `0` comment-stripped `u64`/`i64`/`SHADER_INT64`/float hits. [Cargo.toml](file:///c:/Users/devin/Desktop/lean/con-gpu/Cargo.toml) sets `[profile.release]` `overflow-checks = true`; `con-gpu/target/release/con-gpu.exe` (`10,740,736` bytes) is newer than all `.rs`, `.wgsl`, and `Cargo.toml` inputs.
- **Workspace release tests (`--test-threads=1`):** `35/35` passed, `0` failed, `0` ignored (`15` `con_gpu_arena`, `3` `init_smoke`, `5` `con_gpu`, `6` `con_gpu_lrat`, `6` `con_gpu_shaders`, `exit=0`).
- **Soundness suite (`con-gpu.exe test-soundness`):** `exit=0` — Pipeline B `bignum_nat` `40/40` ops matched; Pipeline C LRAT differential `3` accepted, `7` rejected; corrupt `.olean` files `4/4` rejected; Pipeline A `con-leche` differential `tested=587 accepted=341 rejected=246 gpu_verified=18,260 gpu_rejected=128 delegated=13,079`.

| Benchmark Row (`con-gpu.exe bench --threads 16 --skip-leanchecker`) | Outcome | Decls | GPU Verified / Delegated | GPU Hybrid / Snapshot Time | CPU Rayon (`16t`) |
| :--- | :--- | ---: | ---: | ---: | ---: |
| `Init` | `Accepted` | `63,937` | `21,735` / `42,202` | `5,314.115 ms` (`kernel 2,398.990 ms`) | `5,910.363 ms` |
| `Std` | `Accepted` | `109,213` | `34,920` / `74,293` | `7,216.809 ms` (`kernel 4,315.410 ms`) | `7,628.304 ms` |
| `DownstreamBench` (strict) | `Declined@114126` (`bv_decide` axiom) | `114,770` | `36,388` / `78,382` | `7,830.442 ms` (`kernel 4,146.175 ms`) | `9,021.144 ms` |
| `DownstreamBench` (`--trust-bv-decide-axioms`) | `Accepted` | `114,770` | `36,388` / `78,382` | `9,773.721 ms` (`kernel 6,829.036 ms`) | `9,845.176 ms` |
| `100K` Synthetic LRAT (`cnf=100,000`, `25,001` steps) | `Verified` | — | `25,001` / `0` | `3.058 ms` (`kernel 1.138 ms`) | `46.848 ms` |
| `Pipeline B BignumNat` (`batch_ops=16,384`) | `Verified` | — | `16,384` / `0` | `gpu_kernel=0.541 ms` | — |
| Incremental `Init.Prelude -> Init` | `Accepted` | `63,937` (`skip 2,002`) | `21,212` / `40,723` | `inc_verify=6,332.929 ms` (`e2e 17,699.117 ms`) | — |
| `CGSNAP02` Snapshot (`--snapshot Init`, `210.85 MiB`) | `Accepted` | `63,937` | `21,735` / `42,202` | `snap_verify=5,750.493 ms` (`e2e 8,137.316 ms`) | — |
| Incremental `Std -> DownstreamBench` | `Accepted` | `114,770` (`skip 3,980`) | `34,551` / `76,239` | `inc_verify=8,891.207 ms` (`e2e 24,140.585 ms`) | — |

- **`Mathlib.Data.Real.Basic` (`mathlib4_real_basic_oleans.tar.zst`, `217,474` decls, `--fresh --jobs 16 --trust-bv-decide-axioms`):**
  - Hybrid + `--save-snapshot`: `ACCEPTED`, `eligible=214,460`, `gpu_verified=87,541`, `delegated=129,933`, `load=23,787.096 ms`, `total_verify=11,026.487 ms`, wall `36,690.1 ms` (`snap_bytes=522,515,703`, `e_nodes_words=57,150,658`), `exit=0`.
  - Hybrid `--snapshot` (`CGSNAP02`): `ACCEPTED`, `eligible=214,460`, `gpu_verified=87,592`, `delegated=129,882`, `load=6,227.375 ms`, `total_verify=9,850.165 ms`, wall `16,798.0 ms` (`2.16x` vs CPU wall), `exit=0`.
  - CPU `--jobs 16`: `ACCEPTED`, `load=23,758.199 ms`, `verify=12,017.890 ms`, wall `36,243.1 ms`, `exit=0`.
- **Full `mathlib4 v4.35.0` ([aws_mathlib4_v4.35.0_oleans.tar.zst](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0/aws_mathlib4_v4.35.0_oleans.tar.zst), `9,033` `.olean`s + stock `Init`/`Std`, `775,326` decls, `--fresh --jobs 16 --trust-bv-decide-axioms`):**
  - Hybrid + `--save-snapshot`: `ACCEPTED`, `eligible=768,246`, `gpu_verified=148,140`, `delegated=627,186`, `load=191,142.777 ms`, `total_verify=147,854.977 ms` (`gpu_kernel=39,505.538 ms`, `pcie_upload=1,890.437 ms`, `gpu_readback=1,952.844 ms`, `host_fallback=88,326.245 ms`), wall `357,210.8 ms` (`snap_bytes=3,750,964,420`, `e_nodes_words=435,186,742`), `exit=0`.
  - Hybrid `--snapshot` (`CGSNAP02`): `ACCEPTED`, `eligible=768,246`, `gpu_verified=148,140`, `delegated=627,186`, `load=76,945.363 ms`, `total_verify=123,526.351 ms` (`gpu_kernel=46,785.671 ms`, `pcie_upload=2,831.688 ms`, `gpu_readback=2,828.754 ms`, `host_fallback=71,064.233 ms`), wall `206,873.6 ms`, `exit=0`.

### 7.3 Gate 3 — Stage 2 `lean4`, Multi-Snapshot + `--fork-any` `lean-zygote`, Shaken-Import CoW & Daemon Provenance

- **Source & script checks:** Audited Phase 3 diffs in [compact.h](file:///c:/Users/devin/Desktop/lean/lean4/src/runtime/compact.h), [compact.cpp](file:///c:/Users/devin/Desktop/lean/lean4/src/runtime/compact.cpp), [module.cpp](file:///c:/Users/devin/Desktop/lean/lean4/src/library/module.cpp), [LeanZygoteShim.lean](file:///c:/Users/devin/Desktop/lean/lean-zygote/LeanZygoteShim.lean), [lean_zygote.cpp](file:///c:/Users/devin/Desktop/lean/lean-zygote/lean_zygote.cpp), [Makefile](file:///c:/Users/devin/Desktop/lean/lean-zygote/Makefile), and [lake_fast_build.sh](file:///c:/Users/devin/Desktop/lean/aws-deploy/lake_fast_build.sh). Both [deploy_aws_96vcpu.sh](file:///c:/Users/devin/Desktop/lean/aws-deploy/deploy_aws_96vcpu.sh) and [lake_fast_build.sh](file:///c:/Users/devin/Desktop/lean/aws-deploy/lake_fast_build.sh) have `crlf=0` and pass `bash -n` (`exit=0`).
- **Stage 2 kernel/suite checks (`/home/devin/build-lean4-s2`):** [rc_model.lean](file:///c:/Users/devin/Desktop/lean/lean4/tests/elab/rc_model.lean) `exit=0`; `9/9` adversarial fixtures in [adversarial](file:///c:/Users/devin/Desktop/lean/benchmarks/downstream_bench/adversarial) rejected/flagged; `6/6` Lake tests (`emptyBuild`, `needs`, `failFast`, `lean`, `buildArgs`, `noBuild`) `exit=0`.

| Suite & Configuration (WSL2 Stage 2, `-j 16`, `smaps_rollup`) | Wall Time (s) | Snapshot / Clean-CoW / Fallbacks | Peak Workers | Peak Agg RSS (MB) | Peak Agg PSS (MB) | Peak Agg Private (MB) | Median Worker RSS / Priv (MB) | Stock `leanchecker` |
| :--- | ---: | :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| `DownstreamBench` Cold Stage 2 (`-j 16 --max-memory-mb auto`) | `12.229` | — | `10` | `7,332.59` | `1,391.61` | `705.19` | `733.96` / `72.71` | — |
| `DownstreamBench` Multi-Snapshot + `--fork-any` (`Init` + `DownstreamBench.Prelude`) | `8.209` (`-32.9%`) | `15` / `17` / `0` | `24` | `7,572.05` | `1,611.41` | `1,095.16` | `13.79` / `4.56` | Windows `exit=0` (`138,854.3 ms`); `33/33` `.olean` SHA256 match (`25/25` non-BV) |
| Shaken-Import `41` mods Cold Stage 2 (`-j 16 --max-memory-mb auto`) | `3.275` | — | `11` | `5,600.98` | `1,398.60` | `713.30` | `510.13` / `45.53` | — |
| Shaken-Import `41` mods Clean-Runtime CoW (`--profile none --fork-any`) | `3.366` | `0` / `41` / `0` | `35` | `6,759.20` | `1,194.35` (`-14.6%`) | `623.94` (`-12.5%`) | `101.60` / `15.22` | Linux `exit=0` |

- **Live `con-gpu` daemon build check:** Stage 2 `lake build --wfail -j 16 --max-memory-mb auto --verify-with-con-gpu` on `DownstreamBench` against Windows `con-gpu.exe daemon --addr 0.0.0.0:47831 --trust-bv-decide-axioms` succeeded in `21,210.9 ms` (`exit=0`); `con-gpu.exe verify --daemon-addr 127.0.0.1:47831 --flush --trust-bv-decide-axioms` exited `0` (`ACCEPTED flushed=33 batches=1 total=114770 prefix_skipped=0 eligible=113636 gpu_verified=36382 delegated=78388 host_verified=78388 elapsed_us=10197771`), `STATS` reported `requests=71 verified_decls=114770 rejected_decls=0`, `SHUTDOWN -> BYE`, and unmodified stock Windows `leanchecker.exe --fresh DownstreamBench` passed (`exit=0`, `140,430.7 ms`).

### 7.4 Rule 2 Math Compliance, AWS & Wave L Hygiene

- Verified `~/.gemini/GEMINI.md` Rule 2 across [VERIFICATION_REPORT.md](file:///c:/Users/devin/Desktop/lean/benchmarks/VERIFICATION_REPORT.md), [con-gpu/README.md](file:///c:/Users/devin/Desktop/lean/con-gpu/README.md), [lean-zygote/README.md](file:///c:/Users/devin/Desktop/lean/lean-zygote/README.md), and [aws-deploy/README.md](file:///c:/Users/devin/Desktop/lean/aws-deploy/README.md): `0` banned LaTeX macro commands and `0` unpadded `_` inside inline `$...$` spans.
- Re-checked `aws.exe ec2 describe-instances --region us-east-1`: `0` running or pending `lean4-*` EC2 instances.
- Deleted all temporary unpack directories (`wave_l_real_basic`, `wave_l_full_mathlib`, `wave_l_ds_zyg_lib`, `wave_l_ds_gpu_lib`), `.cgsnap` files, `/tmp/wave_l_*`, and `$SCRATCH` helper scripts, and verified `0` stray `con-gpu`/`lean-zygote`/`lean`/`lake`/`leanchecker` processes on Windows and WSL2.

---

## 8. Phase 4 Independent Verification Audit (`Waves M–P`)

Wave Q independently re-verified every Phase 4 deliverable across [ConGpuProof](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof.lean) (Wave M), [con-gpu](file:///c:/Users/devin/Desktop/lean/con-gpu/Cargo.toml) (Wave N), Stage 2 `lean4` in WSL2 (Wave O), and multi-profile `lean-zygote` + AWS `c7a.24xlarge` artifacts (Wave P).

### 8.1 Gate 1 — Formal Soundness Audit (`con-gpu/proof/`)

- **Forbidden-token scan (`9` `.lean` files):** Both raw and comment-stripped scans for `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `implemented_by`, `extern`, `native_decide`, `bv_decide`, `sorryAx`, and `LC.c` returned **`0` hits** (`raw_hits=0`, `stripped_hits=0`).
- **Clean stock rebuild:** `C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake.exe clean && lake.exe build --wfail` in [con-gpu/proof](file:///c:/Users/devin/Desktop/lean/con-gpu/proof) succeeded (`exit=0`, `10` jobs, `0` warnings, `32,252.8 ms`).
- **Axiom & fresh kernel audit:** `lake.exe env lean ConGpuProof/AxiomAudit.lean` (`exit=0`) verified all **`58/58`** theorems (including the `15` Wave M theorems in [Phase4Soundness.lean](file:///c:/Users/devin/Desktop/lean/con-gpu/proof/ConGpuProof/Phase4Soundness.lean)) depend only on `{propext, Classical.choice, Quot.sound}` (`pagedArenaOffset_lt_pageCap` depends on no axioms). Unmodified stock `leanchecker.exe --fresh ConGpuProof.AxiomAudit` returned **`exit=0`** (`99,445.1 ms`).

### 8.2 Gate 2 — `con-gpu` Static, Differential, Microbench & Full `mathlib4` Audit (RX 7900 XTX Sequential)

- **Repository & static integrity:**
  - `git -C c:/Users/devin/Desktop/lean/vendor/con-ron status -s` is completely empty (`0` edits or untracked files).
  - Comment-stripped static scans returned `0` floating-point hits across all `18` Rust files (`fp_hits=0`) and `0` `u64`/`i64`/`SHADER_INT64` hits across all `9` `.wgsl` shaders (`wg_hits=0`).
  - `con-gpu/target/release/con-gpu.exe` (`11,212,800` bytes) is up-to-date (`0` newer source files).
- **Workspace unit/integration suite:** `cargo test --workspace --manifest-path c:/Users/devin/Desktop/lean/con-gpu/Cargo.toml --release -- --test-threads=1` passed **`38/38`** (`exit=0`, `84,218.4 ms`: `con_gpu_arena` `16`, `init_smoke` `3`, `con_gpu` `5`, `con_gpu_lrat` `6`, `con_gpu_shaders` `8`, `0` failed, `0` ignored).
- **Differential & adversarial soundness (`con-gpu.exe test-soundness`):** Passed (`exit=0`, `295,020.1 ms`):
  - Pipeline B `bignum_nat`: `40/40` limbs/ops matched.
  - Pipeline C LRAT: `3` valid accepted, `7` malformed/corrupted rejected.
  - Corrupt `.olean` suite: `4/4` rejected.
  - Pipeline A `con-leche` differential: `tested=587`, `accepted=341`, `rejected=246` (`gpu_verified=17691`, `gpu_rejected=128`, `delegated=13648`).
- **Sequential local benchmark suite (`con-gpu.exe bench --threads 16 --skip-leanchecker`, `exit=0`, `183,007.4 ms`):**

| Benchmark Target | Outcome / Decls | GPU Verified / Delegated | GPU Hybrid Verify | CPU Rayon (16t) |
| --- | --- | ---: | ---: | ---: |
| `Init` | `Accepted`, `63,937` (`63,306` eligible) | `29,399` / `34,538` | `6,376.652 ms` (kernel `6,026.429 ms`, host fallback `249.712 ms`, load `8,425.972 ms`) | `6,775.464 ms` |
| `Std` | `Accepted`, `109,213` (`108,156` eligible) | `45,781` / `63,432` | `8,858.479 ms` (kernel `8,543.277 ms`, host fallback `105.546 ms`, load `15,487.720 ms`) | `7,730.126 ms` |
| `DownstreamBench` (strict) | `Declined@114126` (`alu_avg_floor._native.bv_decide.ax_1_5`) | — | `8,557.669 ms` | `8,826.467 ms` |
| `DownstreamBench` (`--trust-bv-decide-axioms`) | `Accepted`, `114,770` (`113,636` eligible) | `47,999` / `66,771` | `9,483.918 ms` (kernel `9,199.476 ms`, host fallback `119.946 ms`) | `9,643.283 ms` |
| `100K` Synthetic LRAT | `Accepted` | — | `14.531 ms` (kernel `11.855 ms`) | `71.674 ms` |
| Pipeline B `BignumNat` | `16,384` ops | — | kernel `0.674 ms` | — |
| Incremental `Init/Prelude -> Init` | `prefix_skipped=2,002`, `delta=61,935` | — | `5,816.254 ms` verify (`14,138.720 ms` e2e) | — |
| `CGSNAP03` (`Init`, `211.66 MiB`) | `63,937` decls | `29,347` / `34,590` | save `464.699 ms`; snap load `275.782 ms`, verify `7,350.894 ms`, e2e `7,626.676 ms` | snap load `1,929.508 ms`, verify `5,641.786 ms` |
| Incremental `Std -> DownstreamBench` | `prefix_skipped=3,980`, `delta=110,790` | — | `7,056.339 ms` verify (`20,385.026 ms` e2e) | — |

- **Full `mathlib4 v4.35.0` (`775,326` decls, `768,246` eligible) on RX 7900 XTX (`--fresh --jobs 16 --trust-bv-decide-axioms`):**
  - **Cold Hybrid + `--save-snapshot`:** `exit=0`, total wall `735,170.3 ms`; `[ACCEPTED]`, `gpu_verified=205,727`, `gpu_rejected=0`, `delegated=569,599` (`host_verified_delegated=569,599`), `load=395,708.058 ms`, `pcie_upload=12,595.905 ms`, `gpu_kernel=260,967.711 ms`, `gpu_readback=5,411.893 ms`, `host_fallback=1,082.492 ms`, `total_verify=317,197.441 ms`, `steps_gpu=1,343,100,951`, `max_scratch_words=29,234`, `delegate_reasons=[0, 7080, 6708, 288659, 0, 0, 267152, 0]`, saved `CGSNAP03` snapshot `3,763,908,818` bytes (`e_nodes_words=435,186,742`).
  - **Warm `CGSNAP03` Hybrid (`--snapshot`):** `exit=0`, total wall **`145,117.0 ms`** (**`5.07x` faster** end-to-end vs Cold `735.17s`); `[ACCEPTED]`, `gpu_verified=205,814`, `gpu_rejected=0`, `delegated=569,512`, `load=3,470.563 ms`, `pcie_upload=925.183 ms`, `gpu_kernel=137,873.650 ms`, `gpu_readback=1,389.264 ms`, `host_fallback=511.477 ms`, `total_verify=141,042.355 ms`, `steps_gpu=1,455,428,177`, `max_scratch_words=29,937`, `delegate_reasons=[0, 7080, 6920, 325240, 0, 0, 230272, 0]`.
  - **Warm `CGSNAP03` CPU (`--snapshot`):** `exit=0`, total wall `149,112.9 ms`; `[ACCEPTED]`, `load=31,162.547 ms`, `verify=115,869.157 ms`.

### 8.3 Gate 3 — WSL2 Stage 2 (`/home/devin/build-lean4-s2`), Multi-Profile `lean-zygote` & Provenance

- **Runtime, adversarial & Lake regressions (Stage 2 stripped of `.elan`):**
  - [rc_model.lean](file:///c:/Users/devin/Desktop/lean/lean4/tests/elab/rc_model.lean): `exit=0` (`24,061 ms`).
  - Adversarial fixtures (`9/9`): `sorry_guard.lean` exposed `sorryAx`; `env_hack_axiom.lean` exposed `fakeUnsoundAxiom`; all `7` unsound/ill-typed fixtures exited non-zero.
  - Lake regression suite (`6/6`): `emptyBuild`, `needs`, `failFast`, `lean`, `buildArgs`, `noBuild` all exited `0`.
- **Stage 2 Cold vs Multi-Profile `--fork-any` `lean-zygote` on `DownstreamBench` (`-j 16 --max-memory-mb auto`, `smaps_rollup`):**
  - Note: invoking `--profile module:DownstreamBench.Prelude` fails cleanly (`uncaught exception: cannot import non-module DownstreamBench.Prelude from module`), confirming kernel module/non-module boundary enforcement. Using `--prebuild DownstreamBench.Prelude --profile module:Init --profile DownstreamBench.Prelude --fork-any` loads `profiles=2` (`[0]` `modules=653 imports=2 isModule=true`; `[1]` `modules=1148 imports=3 isModule=false`, `fork-any=on`) via isolated `snap_helpers` and completes cleanly:

| Build Configuration | Elapsed (s) | Speedup | Hit Stats | Peak Agg RSS (MiB) | Peak Agg PSS (MiB) | Median Worker RSS / PSS / Priv (MiB) |
| --- | ---: | ---: | --- | ---: | ---: | --- |
| Stage 2 Cold (`lake build --wfail -j 16`) | `12.108` | `1.00x` | `33` cold workers | `7,476.93` | `1,369.91` | `733.11` / `187.67` / `71.99` |
| Multi-Profile `--fork-any` Zygote (`lake_fast_build.sh`) | `7.368` | **`1.64x`** | `snapshot_hits=15`, `clean_cow_hits=17`, `fallbacks=0` | `6,750.97` | `1,276.88` | `118.26` / **`29.83`** / `16.48` |

- **Bit-identity & Stock Provenance:** SHA256 comparison across all emitted `.olean`s between Stage 2 Cold and Multi-Profile `--fork-any` Zygote showed **`33/33` exact matches** (`25/25` non-BV exact, `diffs=[]`). Unmodified stock WSL2 `v4.35.0` `leanchecker --fresh DownstreamBench` passed (`exit=0`, `136,971 ms`).

### 8.4 Gate 4 — AWS `c7a.24xlarge` Phase 4 Artifact Audit & Cleanup Hygiene

- **Downloaded AWS artifacts ([aws_mathlib4_v4.35.0_phase4](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0_phase4)):** Verified **`35/35`** files match `remote_sha256sums.txt` (`mismatches=0`); verified Phase 2 [aws_mathlib4_v4.35.0](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_mathlib4_v4.35.0) remains intact (**`27/27`** `OK`). `opt_lean_githash.txt` records `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; `cadical_ldd.txt` confirms no `libc++` dependency.
- **Suite JSON & stats checks (`exit_code=0` across all `10` JSON files, `fallbacks=0` across all Zygote runs):**
  - Suite 1 (`Mathlib.Data.Real.Basic`): Stock `65.463s` (RSS `15,832.95 MiB`, PSS `3,796.7 MiB`), Phase 4 Cold `71.32s` (PSS `3,177.81 MiB`, `775/797` SHA256 vs Stock), Phase 4 Multi-Profile `--fork-any` Zygote `82.529s` (PSS `2,960.19 MiB`, `snapshot_hits=40`, `clean_cow_hits=667`, `fallbacks=0`, `797/797` SHA256 vs Phase 4 Cold).
  - Suite 2 (`DownstreamReal`): Stock `93.998s` (RSS `24,436.88 MiB`, PSS `4,492.6 MiB`) vs Phase 4 `--module` Zygote **`6.592s`** (**`14.26x`** faster, RSS `2,823.56 MiB`, PSS `1,718.99 MiB`, `snapshot_hits=96`, `clean_cow_hits=1`, `fallbacks=0`).
  - Suite 3 (Full `Mathlib`, `9,033` `.olean`s): Phase 4 Cold `602.782s` (RSS `63,060.64 MiB`, PSS `13,726.32 MiB`) vs Phase 4 `--fork-any` Zygote `620.804s` (RSS `62,269.42 MiB`, PSS `11,272.67 MiB`, Priv `10,049.27 MiB`, `snapshot_hits=1`, `clean_cow_hits=8,624`, `fallbacks=0`).
  - Suite 4 (Full `Mathlib` verification, `775,357` decls on `c7a.24xlarge`): Stock `leanchecker --fresh Mathlib` `1,480.583s` (RSS `8,746.6 MiB`); `con-gpu` CPU `--save-snapshot` `126.86s` (`load=102,433.196 ms`, `verify=10,607.149 ms`, `3.6G` `CGSNAP03`); `con-gpu` CPU `--snapshot` **`33.67s`** (**`43.97x`** faster vs stock `leanchecker`, `load=21,459.593 ms`, `verify=11,679.454 ms`, `[ACCEPTED]`, RSS `7,412.96 MiB`).
- **EC2 billing, Rule 2 & workspace cleanliness:** `aws.exe ec2 describe-instances --region us-east-1` confirmed `i-049993703bf180ae6` (`lean4-phase4-96vcpu-bench`) is **`terminated`**, `0` running/pending/stopping/stopped `lean4-*` instances exist, and `i-00645567de6802cae` (`vrs-swarm`, `r6a.8xlarge`) remains `stopped`. All temporary mathlib/DownstreamBench directories, `.cgsnap` files, `/tmp/wave_q_*`, and `$SCRATCH` scripts were removed, with `0` lingering `con-gpu`/`lean-zygote`/`lean`/`lake` swarm processes on Windows or WSL2, and `0` Rule 2 math violations across all checked markdown documents.

---

## 9. Phase 5 Lean Ecosystem AWS CPU & GPU Audit (Wave U2)

Wave U2 independently audited all Phase 5 deliverables (`Waves R–T`) across `aws_ecosystem_phase5/` and produced [ecosystem_metrics_master.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/ecosystem_metrics_master.json), [ecosystem_metrics_master.csv](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/ecosystem_metrics_master.csv) (`236` normalized rows), and [ECOSYSTEM_BENCHMARK_REPORT.md](file:///c:/Users/devin/Desktop/lean/benchmarks/ECOSYSTEM_BENCHMARK_REPORT.md).

### 9.1 Artifact Checksum & Static Code Audit

- **SHA256 Checksum Integrity (`356/356` `OK`, `0` missing, `0` mismatches):**
  - [cpu_c7a_96vcpu/remote_sha256sums.txt](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/cpu_c7a_96vcpu/remote_sha256sums.txt): `230/230` OK.
  - [gpu_l40s_g6e/sha256sums.txt](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/gpu_l40s_g6e/sha256sums.txt): `42/42` OK (`ml.g6e.4xlarge`, job `lean4-eco-l40s-c89695-0`, `Completed`, `1,330s`).
  - [gpu_a10g_g5/sha256sums.txt](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/gpu_a10g_g5/sha256sums.txt): `42/42` OK (`ml.g5.8xlarge`, job `lean4-eco-a10g-131829-0`, `Completed`, `1,349s`).
  - [local_rx7900xtx/sha256sums.txt](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/local_rx7900xtx/sha256sums.txt): `42/42` OK (`AMD Radeon RX 7900 XTX`).
- **Static & `vendor/con-ron` Audit:** `git -C c:/Users/devin/Desktop/lean/vendor/con-ron status -s` returned `0` modified/untracked files (`exit=0`); comment-stripped regex scans returned `0` floating-point hits across `18` `.rs` files and `0` `u64`/`i64`/`SHADER_INT64` hits across `9` `.wgsl` files in `con-gpu/crates/`.

### 9.2 100% Mathematical Validation Parity (`Stock leanchecker`, `con-gpu`, `bench-synthetic`, `.olean` Determinism)

- **Stock `leanprover/lean4:v4.35.0` `leanchecker --fresh`:** `13/13` standalone ecosystem packages exited `0` (`SyntheticBench` `75.288s`, `Init_Std` `112.701s`, `Batteries` `65.157s`, `Qq` `53.112s`, `Aesop` `57.566s`, `ImportGraph` `56.800s`, `Plausible` `54.025s`, `DocGen4` `92.439s`, `DownstreamBench` `74.612s`, `Cedar` `196.167s` [`Cedar`, `SymCC`], `Mathlib_Real_Basic` `96.951s`, `Full_Mathlib` `1,483.593s`, `PrimeNumberTheoremAnd` `568.375s`).
- **Multi-Platform `con-gpu` Parity (`96T` EPYC CPU, `NVIDIA L40S`, `NVIDIA A10G`, `AMD RX 7900 XTX`):**
  - Verified identical `total_decls` and verdicts across every platform and mode on all `13/13` closures (`11/11` `[Accepted]` `exit=0`; `Cedar` `173,501` decls `[Declined]` `exit=2` at `112,259` on `native_decide`; `PrimeNumberTheoremAnd` `544,768` decls `[Declined]` `exit=2` at `528,798` on `sorryAx`).
  - Full `mathlib4 v4.35.0` (`775,357` decls) warm `CGSNAP03` speedups vs Stock `leanchecker` (`1,483.593s`): **`47.89x`** (`30.981s`, `96T` EPYC CPU), **`22.81x`** (`65.048s`, `A10G` CPU `32T`) / **`22.25x`** (`66.679s`, `A10G` Hybrid), **`18.22x`** (`81.415s`, `L40S` CPU `16T`) / **`16.98x`** (`87.358s`, `L40S` Hybrid), and **`10.49x`** (`141.364s`, local `RX 7900 XTX` CPU) / **`9.32x`** (`159.179s`, `RX 7900 XTX` Hybrid).
- **Soundness & Scaling Parity (`test-soundness` & `bench-synthetic`):**
  - `test-soundness` passed `4/4` sub-suites and `587/587` `con-leche` differential parity (`341` accepted, `246` rejected, `17,691` GPU-verified) on `L40S`, `A10G`, and `RX 7900 XTX`.
  - `bench-synthetic` passed (`all_passed=true`) across `cpu_16t`, `cpu_48t`, `cpu_96t`, `L40S`, `A10G`, and `RX 7900 XTX`: `100%` `BignumNat` parity (`16K`/`65K`/`262K`) and `delegated_steps=0` + corrupt-clause `Rejected` at `100K`/`500K`/`1M` LRAT (`51.83x` GPU vs CPU on `A10G`, `15.77x` on `L40S`, `6.29x` on `RX 7900 XTX`).
- **`lean-zygote` CoW Determinism, Fallbacks & Memory (`c7a.24xlarge`):**
  - `12/13` Zygote builds recorded `fallbacks=0`, reducing median worker `PSS` by `-49.4%` (`Mathlib_Real_Basic`) to **`-99.9%`** (`PrimeNumberTheoremAnd`) / **`-99.8%`** (`Full_Mathlib`: `193.78 -> 0.36 MiB`, agg PSS `-17.5%`).
  - `DocGen4` recorded `snapshot_hits=1, clean_cow_hits=16, fallbacks=61` (safe cold-spawn fallback on C/FFI `dynlib`s `leansqlite`/`MD4Lean`/`UnicodeBasic`), still completing `exit=0` with `78/78` exact `.olean` SHA256 match.
  - Across the `11` repos with `sha256_compare.txt`, `Cold vs Zygote` non-BV `.olean`s matched **`100%`** in `9/11` repos (`Aesop`, `Batteries`, `DocGen4`, `DownstreamBench`, `ImportGraph`, `Plausible`, `Qq`, `Mathlib_Real_Basic`, `SyntheticBench`), `345/348` in `Cedar`, and `209/210` in `PrimeNumberTheoremAnd` (`Full_Mathlib` emitted `9,031` `.olean`s in both Cold and Zygote).

### 9.3 AWS Billing Isolation & Cleanliness Audit

- Live `aws.exe` queries (`us-east-1`) verified: `0` active/running/stopped `lean4-*` EC2 instances; `0` `InProgress` SageMaker training jobs (`TrainingJobSummaries: []`); `0` `lean4-eco-*` S3 buckets; `0` `lean4-eco-*` ECR repositories (`["nvidia-port"]`); and `0` `lean4-*` IAM roles (`[]`). Pre-existing `vrs-swarm` (`i-00645567de6802cae`), `mathregistry*`, `motemath*`, and `nvidia-port` resources remain untouched.
- Confirmed `~/.gemini/GEMINI.md` Rule 2 math compliance (`banned=0`, `unpadded_inline_underscore=0`) across [ECOSYSTEM_BENCHMARK_REPORT.md](file:///c:/Users/devin/Desktop/lean/benchmarks/ECOSYSTEM_BENCHMARK_REPORT.md), [VERIFICATION_REPORT.md](file:///c:/Users/devin/Desktop/lean/benchmarks/VERIFICATION_REPORT.md), [con-gpu/README.md](file:///c:/Users/devin/Desktop/lean/con-gpu/README.md), [lean-zygote/README.md](file:///c:/Users/devin/Desktop/lean/lean-zygote/README.md), and [aws-deploy/README.md](file:///c:/Users/devin/Desktop/lean/aws-deploy/README.md), and cleaned all Wave U2 scratch scripts and checked zero leftover temp/process artifacts.

---

<!-- generated Phase 6 metrics begin -->

## 10. Phase 6 verification



The c7a stock checker exited 0 for both roots. The con-gpu rows use the corrected verifier, which accepted Full Mathlib and declined PrimeNumberTheoremAnd at declaration 528744 for use of the sorryAx axiom.
The c7a CPU audit covers 14 stock checks, 78 thread-scaling measurements and 13 cold checks on the shared inputs. [CPU audit](aws_ecosystem_phase6/phase6_cpu_parity_audit.json)

Compared 50 L40S and 50 A10G measurements across 13 packages with their RX references. The GPU identity, verdict, exit code, declaration count and GPU rejection checks passed for the modes in the comparison receipt.
The c7a 96-thread cold replay agreed with RX hybrid and with CPU and hybrid mode on both NVIDIA hosts for all 13 shared-input packages. [CPU scaling and four-platform comparison](aws_ecosystem_phase6/phase6_cpu_parity_audit.json)

The corrected RX PNT replay processed 544,714 declarations with 0 GPU rejections. Its earlier Phase 6 run recorded one GPU rejection for a missing sorryAx slot at declaration 540915. [Targeted host and RX replay](aws_ecosystem_phase6/pnt_540915_replay/README.md)

The c7a tail and SageMaker used the corrected Linux verifier with SHA-256 `fd85a90466dbc7454befb4880f9030f74044b7aa74d194550107216c850400ac`. The two-root input archive SHA-256 was `9bab321de7b326d5b0d6aa42f8168c74c3fed11e239364dfc84e535c6fa1bea6`. Validated 664 receipt entries across 9 manifests.

Archived Full_Mathlib builds matched non-BV .olean hashes on 8,960/9,031 for stock versus Phase 6 cold and 9,031/9,031 for Phase 6 cold versus zygote. [Build comparison](aws_ecosystem_phase6/cpu_c7a_96vcpu/full_mathlib_sha256_compare.txt)
Archived Cedar builds matched non-BV .olean hashes on 334/348 for stock versus Phase 6 cold and 345/348 for Phase 6 cold versus zygote. [Build comparison](aws_ecosystem_phase6/cpu_c7a_96vcpu/cedar_sha256_compare.txt)

[Measured rows (CSV)](aws_ecosystem_phase6/phase6_metrics_master.csv) | [Metrics and receipt hashes (JSON)](aws_ecosystem_phase6/phase6_metrics_master.json) | [NVIDIA comparison](aws_ecosystem_phase6/nvidia_parity.json)

<!-- generated Phase 6 metrics end -->

## 11. Verification of the cache-correction benchmarks

The source-build rerun covered 26 archived build cases and seven elaborator profiles on each green compiler. All 33 completed on `v4.35.0-fast`. On `master`, 10 builds and seven profiles completed on the original inputs, 13 builds failed, and three required outputs those builds could not produce. The timing comparison checks compiler commits, source revisions, build logs and compiled module sets. It reports separately timed November source ports and records the original failures alongside them.

The corrected cache participates in Lean source elaboration. The Phase 6 CPU and GPU verifier measurements in section 10 used previously compiled `.olean` inputs. [Comparison, provenance and evidence](aws_ecosystem_phase6/cache_correction/comparison.md)
