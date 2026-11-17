# Phase 6 cache correction benchmarks

The published baseline used Stage 2 Lean 4.35.0 on a c7a.24xlarge with 96 vCPUs. Build values are elapsed seconds. Profile values are milliseconds in the Lean profiler’s cumulative elaboration counter. The first two tables compare with those published results. The paired controls below compare builds before and after the cache correction within each compiler branch.

- `v4.35.0-fast` at `2b82eb00f8` on c7a.24xlarge recorded 33 successful out of 33 cases.
- `master` at `bed19d08b0` on c7a.24xlarge recorded 13 failed, 3 blocked by prerequisites, 17 successful out of 33 cases.

Percentages give the elapsed-time change from the published baseline for matching inputs, build work and instance type. Negative values indicate a shorter run. The cloud runs used native Stage 2 builds at each green commit, matching the original build configuration. The master comparison includes the compiler version change to 4.37.0-pre. Each historical comparison uses one run per cell. Cold builds started with fresh root Lake outputs. The run order differed from the original suite, and OS page-cache state was uncontrolled.

### Lake builds (seconds)

| Published case | Phase 6 | v4.35.0-fast | master |
| --- | ---: | ---: | ---: |
| `aesop_p6_cold` | 19.07 | 19.112 (+0.2%) | failed |
| `aesop_p6_zygote` | 18.527 | 18.590 (+0.3%) | failed |
| `batteries_p6_cold` | 10.137 | 10.130 (-0.1%) | failed |
| `batteries_p6_zygote` | 9.935 | 10.002 (+0.7%) | failed |
| `cedar_p6_cold` | 84.13 | 84.846 (+0.9%) | failed |
| `cedar_p6_zygote` | 82.148 | 82.973 (+1.0%) | failed |
| `doc_gen4_p6_cold` | 39.839 | 40.132 (+0.7%) | failed |
| `doc_gen4_p6_zygote` | 40.61 | 40.728 (+0.3%) | failed |
| `downstream_bench_p6_cold` | 3.22 | 3.187 (-1.0%) | 2.823 (-12.3%) |
| `downstream_bench_p6_zygote` | 3.499 | 3.541 (+1.2%) | 2.873 (-17.9%) |
| `downstream_real_p6_cold` | 86.464 | 92.356 (275 extra modules) | prerequisite failed |
| `downstream_real_p6_zygote` | 68.163 | 73.630 (275 extra modules) | prerequisite failed |
| `full_mathlib_p6_cold` | 547.962 | 540.414 (-1.4%) | failed |
| `full_mathlib_p6_zygote_fork_any` | 542.141 | 533.030 (-1.7%) | prerequisite failed |
| `import_graph_p6_cold` | 7.615 | 7.580 (-0.5%) | failed |
| `import_graph_p6_zygote` | 8.064 | 8.000 (-0.8%) | failed |
| `plausible_p6_cold` | 3.419 | 3.422 (+0.1%) | 2.909 (-14.9%) |
| `plausible_p6_zygote` | 3.371 | 3.406 (+1.0%) | 2.892 (-14.2%) |
| `qq_p6_cold` | 6.697 | 6.653 (-0.7%) | 5.551 (-17.1%) |
| `qq_p6_zygote` | 6.707 | 6.712 (+0.1%) | 5.555 (-17.2%) |
| `real_basic_p6_cold` | 64.312 | 64.937 (+1.0%) | failed |
| `real_basic_p6_zygote` | 67.701 | 68.225 (+0.8%) | failed |
| `synthetic_p6_cold` | 2.609 | 2.525 (-3.2%) | 2.059 (-21.1%) |
| `synthetic_p6_cold_j16` | 3.804 | 3.866 (+1.6%) | 3.000 (-21.1%) |
| `synthetic_p6_cold_j48` | 2.922 | 2.904 (-0.6%) | 2.353 (-19.5%) |
| `synthetic_p6_zygote` | 2.695 | 2.733 (+1.4%) | 2.071 (-23.2%) |

On master, the published Lean 4.35 sources encounter compiler and API changes. For example, pinned Batteries and ImportGraph use the removed `Lean.Environment.const2ModIdx` field. The failed Full Mathlib and Mathlib.Data.Real.Basic cold builds left three dependent measurements without their required inputs.

Both fast DownstreamReal runs compiled 275 additional modules. Their wall times are shown without a percentage because the amount of compiled work changed.

### Synthetic elaboration profiles (milliseconds)

| Published case | Phase 6 | v4.35.0-fast | master |
| --- | ---: | ---: | ---: |
| `synthetic_profile_S1_WhnfTower` | 285 | 344.00 (+20.7%) | 318.00 (+11.6%) |
| `synthetic_profile_S2_TypeclassDiamond` | 334 | 358.00 (+7.2%) | 303.00 (-9.3%) |
| `synthetic_profile_S3_SimpRewriteBank` | 491 | 505.00 (+2.9%) | 468.00 (-4.7%) |
| `synthetic_profile_S4_GrindCongruence` | 71.5 | 71.70 (+0.3%) | 67.50 (-5.6%) |
| `synthetic_profile_S5_BvDecideHardware` | 137 | 133.00 (-2.9%) | 122.00 (-10.9%) |
| `synthetic_profile_S6_BigNatCrypto2048` | 750 | 762.00 (+1.6%) | 184.00 (-75.5%) |
| `synthetic_s5_bv_congpu` | 202 | 178.00 (-11.9%) | 190.00 (-5.9%) |

### Master on the newer downstream corpus

The additional builds used [downstream-lean4 at `308730c4b2`](https://github.com/leanprover/downstream-lean4/tree/308730c4b2152d7235458fde7dcd22eda85bbf3b). These times use different source revisions from the published 4.35 inputs.

| Case | Master elapsed (s) | Compiled modules |
| --- | ---: | ---: |
| `aesop_p6_cold` | 16.077 | 167 |
| `aesop_p6_zygote` | 15.282 | 167 |
| `batteries_p6_cold` | 7.916 | 188 |
| `batteries_p6_zygote` | 7.671 | 188 |
| `doc_gen4_p6_cold` | 32.345 | 77 |
| `doc_gen4_p6_zygote` | 32.989 | 77 |
| `downstream_real_p6_cold` | 4.219 | 97 |
| `downstream_real_p6_zygote` | 4.684 | 97 |
| `full_mathlib_p6_cold` | 406.534 | 9119 |
| `full_mathlib_p6_zygote_fork_any` | 399.030 | 8715 |
| `import_graph_p6_cold` | 7.004 | 54 |
| `import_graph_p6_zygote` | 7.137 | 54 |
| `real_basic_p6_cold` | 51.960 | 814 |
| `real_basic_p6_zygote` | 49.499 | 814 |

The initial DownstreamReal package manifest resolved incompatible dependencies. The reported successful retries used a complete local manifest for the same pinned source. The archive preserves both attempts and the Real.Basic preparation run used by the retry.

Cedar’s published project targets 4.35.0 and failed on master. The downstream nightly corpus contains no Cedar port.

### Before and after the correction on c7a

One paired run compares each green compiler with its own pre-correction build, `4f98a0c3ec` on fast and `4fa92d632b` on master. Percentages require matching source and compiled module sets.

| Branch | Corpus | Case | Before (s) | After (s) | Change |
| --- | --- | --- | ---: | ---: | ---: |
| `v4.35.0-fast` | Phase 6 | `downstream_real_p6_cold` | 91.791 | 92.356 | +0.62% |
| `v4.35.0-fast` | Phase 6 | `downstream_real_p6_zygote` | 73.736 | 73.630 | -0.14% |
| `v4.35.0-fast` | Phase 6 | `real_basic_p6_cold` | 64.634 | 64.937 | +0.47% |
| `master` | Phase 6 | `downstream_bench_p6_cold` | 2.709 | 2.823 | +4.21% |
| `master` | Phase 6 | `synthetic_p6_cold` | 2.009 | 2.059 | +2.49% |
| `master` | downstream nightly | `full_mathlib_p6_cold` | 406.382 | 406.534 | +0.04% |
| `master` | downstream nightly | `full_mathlib_p6_zygote_fork_any` | 398.219 | 399.030 | +0.20% |

### Paired builds on WSL

On a shared Ryzen 7 3700X host, each compiler used four Lake jobs and one Lean thread per child. Each workload had a warm-up followed by four before/after pairs with alternating order. The table reports medians in seconds and the range of paired changes.

| Branch | Workload | Before | After | Change of medians | Paired range |
| --- | --- | ---: | ---: | ---: | ---: |
| `v4.35.0-fast` | SyntheticBench | 32.545 | 31.565 | -3.0% | -16.9% to +26.0% |
| `master` | SyntheticBench | 22.310 | 18.624 | -16.5% | -18.5% to +3.9% |
| `v4.35.0-fast` | DownstreamBench | 13.842 | 14.188 | +2.5% | -11.1% to +24.8% |
| `master` | DownstreamBench | 9.260 | 9.723 | +5.0% | -22.7% to +20.6% |

All four ranges contain both increases and decreases.

The evidence archive contains the measured receipts and their build or profiler logs. [Comparison data](comparison.json) · [Benchmark evidence](evidence.zip)

To inspect the local paired timings after extracting the archive, run `jq '.summary[] | {branch, workload, before_median_seconds, after_median_seconds, paired_percent_change_range}' wsl_matched_cache_controls.json`.
