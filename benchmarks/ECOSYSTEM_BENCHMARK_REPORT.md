# Phase 5 Lean 4 Ecosystem Benchmark & Multi-GPU Verification Report

**Scope:** Cross-platform evaluation of Stage 2 `lean4`, multi-profile `lean-zygote` CoW builds, `con-gpu` hybrid/CPU formal verification (`CGSNAP03` snapshots + `--verify-olean-hashes`), and unmodified Stock `leanprover/lean4:v4.35.0` `leanchecker --fresh` validation across **13 self-contained `.olean` closures** and **14 build suites** spanning synthetic stress suites, real-world ecosystem libraries, and `mathlib4 v4.35.0`.  
**Master Datasets:** [ecosystem_metrics_master.json](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/ecosystem_metrics_master.json) | [ecosystem_metrics_master.csv](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/ecosystem_metrics_master.csv) (`236` rows)  
**Detailed Verification Audit:** [VERIFICATION_REPORT.md](file:///c:/Users/devin/Desktop/lean/benchmarks/VERIFICATION_REPORT.md#L275-L345) (Section 9)

---

## 1. Testbed & Platforms

| Platform ID | Hardware / Instance | CPU Threads | GPU / Driver | Artifact Directory |
| --- | --- | ---: | --- | --- |
| `aws_c7a_96vcpu` | AWS EC2 `c7a.24xlarge` (`AMD EPYC 9R14`, `184 GiB` RAM) | `96` (also `16`/`48` sweep) | CPU `rayon` | [cpu_c7a_96vcpu](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/cpu_c7a_96vcpu) (`230/230` SHA256 OK) |
| `aws_sagemaker_l40s` | AWS SageMaker `ml.g6e.4xlarge` (`EPYC 7R13`, billable `1,330s`) | `16` | `NVIDIA L40S` (`Vulkan`, driver `595.112.07`) | [gpu_l40s_g6e](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/gpu_l40s_g6e) (`42/42` SHA256 OK) |
| `aws_sagemaker_a10g` | AWS SageMaker `ml.g5.8xlarge` (`EPYC 7R32`, billable `1,349s`) | `32` | `NVIDIA A10G` (`Vulkan`, driver `550.144.03`) | [gpu_a10g_g5](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/gpu_a10g_g5) (`42/42` SHA256 OK) |
| `local_rx7900xtx` | Local Windows 11 + WSL2 host | `16` | `AMD Radeon RX 7900 XTX` (`Vulkan`) | [local_rx7900xtx](file:///c:/Users/devin/Desktop/lean/benchmarks/aws_ecosystem_phase5/local_rx7900xtx) (`42/42` SHA256 OK) |

---

## 2. Category 1 — Synthetic Stress Suites (`SyntheticBench` & `bench-synthetic`)

### 2.1 `SyntheticBench` (`72` modules, `117,461` decls)

- **Build & Memory (`c7a.24xlarge`, `96` vCPUs):** Stock `v4.35.0` `2.589s` (Peak Agg RSS `11,556.56 MiB`, PSS `1,443.72 MiB`), Stage 2 Cold `2.672s` (`4.18s` at `-j 16`, `3.056s` at `-j 48`; Agg RSS `13,060.36 MiB`, PSS `1,253.17 MiB`), Stage 2 Zygote `2.857s` (`snapshot_hits=70`, `clean_cow_hits=1`, `fallbacks=0`; **Agg RSS `2,107.41 MiB` `-83.9%`**, Agg PSS `1,049.48 MiB`, **median worker PSS `61.88 -> 0.26 MiB` `-99.6%`**). `71/71` non-BV `.olean`s matched SHA256 bit-for-bit (`Stock vs Cold` and `Cold vs Zygote`).
- **Verification (`117,461` decls):** Stock `leanchecker --fresh SyntheticBench` `75.288s` (`exit=0`) vs `con-gpu`:
  - `96T` EPYC CPU `CGSNAP03`: **`2.651s`** (**`28.40x` faster**; `load=1.902s`, `verify=0.748s`).
  - `NVIDIA A10G` `CGSNAP03` Hybrid: **`6.130s`** (**`12.28x`**; `gpu_verified=44,794`); `cpu_snap`: `5.238s` (`14.37x`).
  - `NVIDIA L40S` `CGSNAP03` Hybrid: **`7.032s`** (**`10.71x`**; `gpu_verified=48,761`); `cpu_snap`: `6.578s` (`11.45x`).
  - `AMD RX 7900 XTX` `CGSNAP03` Hybrid: **`12.738s`** (**`5.91x`**; `gpu_verified=48,914`).

### 2.2 Pure GPU Kernel Scaling (`con-gpu bench-synthetic`, `all_passed=true` on all 4 platforms)

All `BignumNat` runs passed `100%` exact `u32`-limb host parity; all `LRAT` runs had `delegated_steps=0` and rejected corrupted clauses (`corrupt_rejected_gpu=true`, `corrupt_rejected_cpu=true`):

| Suite & Scale | `96T` EPYC CPU (`cpu_96t`) | `NVIDIA L40S` (`gpu_tot` / `kern` / `cpu16`) | `NVIDIA A10G` (`gpu_tot` / `kern` / `cpu32`) | `AMD RX 7900 XTX` (`gpu_tot` / `kern` / `cpu16`) |
| --- | ---: | ---: | ---: | ---: |
| `BignumNat` `16,384` ops | `1.593 ms` | `7.710 ms` / `0.458 ms` / `0.422 ms` | `10.307 ms` / `0.570 ms` / `0.886 ms` | `20.989 ms` / `2.683 ms` / `1.368 ms` |
| `BignumNat` `65,536` ops | `2.113 ms` | `6.845 ms` / `0.148 ms` / `1.252 ms` | `8.003 ms` / `0.200 ms` / `1.229 ms` | `7.919 ms` / `0.590 ms` / `3.366 ms` |
| `BignumNat` `262,144` ops | `3.767 ms` | `28.542 ms` / `0.267 ms` / `4.069 ms` | `31.187 ms` / `0.324 ms` / `3.345 ms` | `26.249 ms` / `1.470 ms` / `11.185 ms` |
| `LRAT` `100K` (`25,001` steps) | `6.668 ms` | `1.394 ms` / `0.224 ms` / `4.556 ms` (**`3.27x`**) | `1.421 ms` / `0.254 ms` / `7.076 ms` (**`4.98x`**) | `1.922 ms` / `0.713 ms` / `17.944 ms` (**`9.34x`**) |
| `LRAT` `500K` (`125,001` steps) | `22.343 ms` | `7.827 ms` / `0.375 ms` / `22.051 ms` (**`2.82x`**) | `7.953 ms` / `0.498 ms` / `59.696 ms` (**`7.51x`**) | `6.071 ms` / `1.442 ms` / `48.333 ms` (**`7.96x`**) |
| `LRAT` `1M` (`250,001` steps) | `62.923 ms` | **`15.546 ms`** / **`0.549 ms`** / `245.097 ms` (**`15.77x`**) | `15.750 ms` / `0.754 ms` / `816.342 ms` (**`51.83x`**) | **`11.222 ms`** / `2.716 ms` / `70.563 ms` (**`6.29x`**) |

*(At `16T` and `48T` on EPYC `c7a.24xlarge`, `1M`-clause LRAT CPU `rayon` took `13.621 ms` and `23.684 ms`, respectively — showing NUMA/cross-CCX contention above `16` CPU threads, whereas all 3 GPUs hold ~`11–16 ms` flat total including PCIe upload.)*

---

## 3. Category 2 — Real-World Ecosystem Repositories

### 3.1 Build & `lean-zygote` CoW Memory (`c7a.24xlarge`)

| Package | Stock Build (s) | Stage 2 Cold (s) | Stage 2 Zygote (s) | Zygote Hits (`snap / cow / fb`) | Median Worker PSS (`Cold -> Zygote`) | `Cold vs Zygote` SHA256 (non-BV) |
| --- | ---: | ---: | ---: | --- | ---: | ---: |
| `Batteries` | `10.320` | `17.929` | `20.625` | `32 / 164 / 0` | `86.63 -> 7.20 MiB` (`-91.7%`) | `196/196` |
| `Qq` | `6.591` | `7.417` | `7.417` | `0 / 14 / 0` | `242.37 -> 59.61 MiB` (`-75.4%`) | `14/14` |
| `Aesop` | `19.072` | `21.041` | `20.487` | `7 / 160 / 0` | `133.67 -> 7.45 MiB` (`-94.4%`) | `167/167` |
| `ImportGraph` | `6.775` | `10.925` | `11.187` | `0 / 49 / 0` | `72.68 -> 22.44 MiB` (`-69.1%`) | `49/49` |
| `Plausible` | `3.407` | `3.668` | `3.577` | `0 / 13 / 0` | `271.15 -> 81.73 MiB` (`-69.9%`) | `13/13` |
| `DocGen4` | `35.717` | `58.118` | `58.443` | `1 / 16 / 61` | `61.30 -> 55.23 MiB` (`-9.9%`) | `78/78` |
| `Cedar` | `86.224` | `145.619` | `155.341` | `16 / 332 / 0` | `111.59 -> 1.11 MiB` (`-99.0%`) | `345/348` |
| `DownstreamBench` | `3.348` | `3.595` | `3.703` | `15 / 17 / 0` | `134.73 -> 0.71 MiB` (`-99.5%`) | `22/22` |
| `DownstreamReal` | `32.194` | `103.170` | `92.695` | `0 / 578 / 0` | `143.57 -> 1.71 MiB` (`-98.8%`) | — |

*(Note: `DocGen4` uses compiled C/FFI `dynlib`s such as `leansqlite`, `MD4Lean`, and `UnicodeBasic`, so `lean-zygote` safely fell back to cold `lean` on `61` plugin-loading modules while still matching `78/78` `.olean` SHA256s.)*

### 3.2 Multi-Platform Verification Comparison (`Init_Std` & Category 2 Closures)

| Closure | Total Decls | Verdict (All 4 Plats) | Stock `leanchecker` (s) | `96T` EPYC `CGSNAP03` (s) | `L40S` Hybrid `CGSNAP03` (s) | `A10G` Hybrid `CGSNAP03` (s) | `RX 7900 XTX` Hybrid `CGSNAP03` (s) |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| `Init_Std` | `113,257` | `Accepted` (`ec=0`) | `112.701` | **`2.612`** (`43.14x`) | `6.923` (`16.28x`) | `5.861` (`19.23x`) | `12.150` (`9.28x`) |
| `Qq` | `100,077` | `Accepted` (`ec=0`) | `53.112` | **`2.411`** (`22.03x`) | `5.665` (`9.38x`) | `5.082` (`10.45x`) | `10.740` (`4.95x`) |
| `Plausible` | `104,626` | `Accepted` (`ec=0`) | `54.025` | **`2.427`** (`22.26x`) | `5.658` (`9.55x`) | `5.117` (`10.56x`) | `8.987` (`6.01x`) |
| `DownstreamBench` | `114,770` | `Accepted` (`ec=0`) | `74.612` | **`2.665`** (`28.00x`) | `7.021` (`10.63x`) | `5.917` (`12.61x`) | `11.719` (`6.37x`) |
| `ImportGraph` | `119,017` | `Accepted` (`ec=0`) | `56.800` | **`2.451`** (`23.17x`) | `6.016` (`9.44x`) | `5.161` (`11.01x`) | `10.552` (`5.38x`) |
| `Aesop` | `122,266` | `Accepted` (`ec=0`) | `57.566` | **`2.477`** (`23.24x`) | `5.995` (`9.60x`) | `5.230` (`11.01x`) | `13.850` (`4.16x`) |
| `Batteries` | `129,782` | `Accepted` (`ec=0`) | `65.157` | **`3.097`** (`21.04x`) | `6.484` (`10.05x`) | `5.667` (`11.50x`) | `10.497` (`6.21x`) |
| `DocGen4` | `200,853` | `Accepted` (`ec=0`) | `92.439` | **`3.088`** (`29.94x`) | `8.172` (`11.31x`) | `6.930` (`13.34x`) | `13.059` (`7.08x`) |
| `Cedar` (Cold only) | `173,501` | `Declined` (`ec=2`, `native_decide`) | `196.167` | `14.897` (cold) | `21.750` (cold) | `23.240` (cold) | `41.461` (cold) |

---

## 4. Category 3 — `mathlib4 v4.35.0` & `PrimeNumberTheoremAnd`

### 4.1 Build & `lean-zygote` CoW Memory (`c7a.24xlarge`)

- **`Mathlib.Data.Real.Basic` (`217,505` decls):** Stock `65.570s` (Agg RSS `15,163.51 MiB`, PSS `3,368.93 MiB`), Stage 2 Cold `70.622s` (Agg RSS `16,443.43 MiB`, PSS `3,483.97 MiB`), Stage 2 Zygote `83.780s` (`snapshot_hits=40`, `clean_cow_hits=667`, `fallbacks=0`; Agg RSS `13,993.32 MiB`, Agg PSS `2,999.82 MiB`, median worker PSS `131.63 -> 66.67 MiB`, **`797/797` Cold vs Zygote SHA256 match**).
- **Full `mathlib4 v4.35.0` (`775,357` decls, `9,031` built `.olean`s):** Stock `96c` `583.999s` (Agg RSS `68,307.94 MiB`, PSS `13,681.72 MiB`), Stage 2 Cold `601.937s` (Agg RSS `62,875.34 MiB`, PSS `13,993.83 MiB`), Stage 2 `--fork-any` Zygote `620.424s` (`snapshot_hits=1`, `clean_cow_hits=8,624`, `fallbacks=0`; **Agg PSS `11,542.95 MiB` `-17.5%`**, **median worker PSS `193.78 -> 0.36 MiB` `-99.8%`**).
- **`PrimeNumberTheoremAnd` (`544,768` decls):** Stock `117.926s` (Agg PSS `10,232.62 MiB`), Stage 2 Cold `125.347s`, Stage 2 Zygote `161.806s` (`snapshot_hits=1`, `clean_cow_hits=209`, `fallbacks=0`; Agg PSS `8,382.92 MiB`, **median worker PSS `593.51 -> 0.51 MiB` `-99.9%`**, `209/210` Cold vs Zygote SHA256 match).

### 4.2 Full `mathlib4` & `Mathlib.Data.Real.Basic` Verification Scaling

| Closure / Mode | Stock `leanchecker` | `96T` EPYC CPU | `NVIDIA L40S` (`16T` host) | `NVIDIA A10G` (`32T` host) | `AMD RX 7900 XTX` (`16T` host) |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Mathlib.Data.Real.Basic` (`217,505` decls) — Cold | `96.951s` | `15.329s` (`6.32x`) | `20.787s` (`4.66x`) | `22.869s` (`4.24x`) | `42.472s` (`2.28x`) |
| `Mathlib.Data.Real.Basic` — Warm `CGSNAP03` Hybrid / CPU | — | **`3.212s`** (`30.18x`) | `8.770s` / `7.929s` | `7.274s` / `6.265s` | `13.589s` / `27.241s` |
| `Mathlib.Data.Real.Basic` — `CGSNAP03` `--verify-olean-hashes` | — | — | `8.628s` (`load=0.776s`) | `7.143s` (`load=0.783s`) | `25.451s` (`load=1.926s`) |
| `Full_Mathlib` (`775,357` decls) — Cold Hybrid / CPU | `1,483.593s` | `120.583s` (`12.30x`) | `179.290s` (`8.27x`) | `182.952s` (`8.11x`) | `317.726s` (`4.67x`) |
| `Full_Mathlib` — Warm `CGSNAP03` Hybrid | — | — | `87.358s` (`16.98x`, `load=4.567s`) | `66.679s` (`22.25x`, `load=4.572s`) | `159.179s` (`9.32x`, `load=3.849s`) |
| `Full_Mathlib` — Warm `CGSNAP03` CPU | — | **`30.981s`** (**`47.89x`**) | `81.415s` (`18.22x`) | `65.048s` (`22.81x`) | `141.364s` (`10.49x`) |
| `Full_Mathlib` — `CGSNAP03` `--verify-olean-hashes` | — | — | `87.354s` (`load=5.103s`) | `67.176s` (`load=5.060s`) | `159.450s` (`load=20.300s`) |
| `PrimeNumberTheoremAnd` (`544,768`, `[Declined]` `sorryAx` `@528798`) | `568.375s` (`ec=0`) | `56.110s` (cold `ec=2`) | `87.705s` / `78.486s` (`ec=2`) | `90.056s` / `82.679s` (`ec=2`) | `165.886s` / `132.732s` (`ec=2`) |

*CPU thread scaling on `c7a.24xlarge` (`Full_Mathlib`, `775,357` decls):* Cold `16T` `131.813s` (`verify=35.483s`) -> `48T` `110.074s` (`verify=12.047s`) -> `96T` `120.583s` (`verify=11.206s`); Warm `CGSNAP03` `16T` `52.649s` (`verify=31.960s`) -> `48T` `33.620s` (`verify=12.538s`) -> `96T` **`30.981s`** (`verify=10.148s`).

---

## 5. Multi-GPU Architecture Comparison (`L40S` vs `A10G` vs `RX 7900 XTX`) & Key Findings

1. **Pure Vulkan GPU Compute (`LRAT` / `BignumNat`):** When host delegation is `0`, `NVIDIA L40S` achieves the fastest raw kernel execution (`0.549 ms` at `1M`-clause LRAT vs `0.754 ms` on `A10G` and `2.716 ms` on `RX 7900 XTX`), while `RX 7900 XTX` local PCIe upload (`7.217 ms`) gives it the fastest `1M`-clause total GPU time (`11.222 ms` vs `15.546 ms` `L40S`, `15.750 ms` `A10G`).
2. **Host-Delegated Hybrid Verification (`Full_Mathlib`):** `201k–206k` declarations verify on the GPU, while `~570k` universe/inductive/meta declarations run on the host Rayon pool. Therefore, `ml.g5.8xlarge` (`32` vCPUs, `A10G`) completes warm `Full_Mathlib` in `66.679s` vs `87.358s` on `ml.g6e.4xlarge` (`16` vCPUs, `L40S`) and `30.981s` on `96`-vCPU EPYC `c7a.24xlarge`.
3. **`CGSNAP03` Load Elimination:** Binary arena snapshots cut `Full_Mathlib` load time by **`39.4x–46.5x`** (`179.001s -> 3.849s` on Windows `RX 7900 XTX`; `120.331s -> 4.572s` on `A10G`; `96.898s -> 4.567s` on `L40S`). Even with `--verify-olean-hashes`, load overhead adds only `0.5s` on Linux SageMaker instances (`4.572s -> 5.060s` on `A10G`, `4.567s -> 5.103s` on `L40S`).

---

## 6. 100% Mathematical Validation & Soundness Summary

- **Stock `leanchecker --fresh`:** `13/13` verification suites exited `0` cleanly.
- **`con-gpu` Parity across all `4` platforms:** `100%` identical `total_decls` and verdicts on all `13/13` closures (`11/11` `[Accepted]` `exit=0`; `Cedar` `173,501` and `PrimeNumberTheoremAnd` `544,768` `[Declined]` `exit=2` on unapproved axioms `native_decide` and `sorryAx`).
- **Soundness Suites (`test-soundness` on `L40S`, `A10G`, `RX 7900 XTX`):** `4/4` sub-suites passed on every GPU (`40/40` `BignumNat`, `3/7` LRAT accept/reject, `4/4` corrupt `.olean` rejection, `587/587` `con-leche` differential parity).
- **Static & Repository Integrity:** `vendor/con-ron` `git status -s` clean; `0` floating-point ops across `18` Rust files in `con-gpu/crates/`; `0` `u64`/`i64`/`SHADER_INT64` hits across `9` `.wgsl` shaders.
