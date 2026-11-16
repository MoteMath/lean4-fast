# Stock Lean v4.35.0 Baseline Measurements

Suite: [downstream_bench](file:///c:/Users/devin/Desktop/lean/benchmarks/downstream_bench/lakefile.toml) (33 interdependent `.lean` modules across 5 DAG layers importing `Std` + `Init`, emitting 33 `.olean` files totaling 10,308,048 bytes, plus 9 adversarial fixtures in [adversarial](file:///c:/Users/devin/Desktop/lean/benchmarks/downstream_bench/adversarial)).

## 1. Hardware & Toolchains Observed
- **Windows 11**: 16 logical CPUs (AMD Ryzen 7 3700X), 32 GiB RAM, AMD Radeon RX 7900 XTX (`Driver 32.0.31041.1004`).
- **WSL2 Ubuntu Linux (`6.6.87.2-microsoft-standard-WSL2`)**: 16 logical CPUs, 23 GiB RAM + 6 GiB Swap.
- **Stock Toolchain**: `Lean (version 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`, `Lake version 5.0.0-src+eb6cafb`.

## 2. Stock Build & Verification Baselines

| Benchmark / Check | Platform | Wall-Clock (s) | Memory / Notes | Source |
| :--- | :--- | ---: | :--- | :--- |
| Clean `lake build` (`DownstreamBench`, 35 jobs) | WSL2 Linux (ext4) | 9.714 | 15 peak concurrent workers; 10,814.17 MB agg RSS; 1,607.92 MB agg PSS; 884.85 MB agg private; max worker 770.29 MB RSS / 722.75 MB PSS / 682.82 MB private | [baseline_stock_linux.json](file:///c:/Users/devin/Desktop/lean/benchmarks/baseline_stock_linux.json) |
| Clean `lake.exe build --wfail` (`DownstreamBench`, 35 jobs) | Windows 11 | 22.586 | Exit 0, zero warnings | `lake.exe build --wfail` |
| Single-worker `import Std` | WSL2 Linux | 0.770 | 755,828 KB (~738.1 MiB) max RSS | `/usr/bin/time -v` |
| Single-worker `import Std` + `import Lean` | WSL2 Linux | 2.070 | 1,562,064 KB (~1,525.5 MiB) max RSS (`1,038,432 kB` Private_Clean + `110,388 kB` Private_Dirty in `/proc/<pid>/smaps_rollup`) | `/usr/bin/time -v` & `smaps_rollup` |
| `leanchecker.exe DownstreamBench` (parallel replay) | Windows 11 | 27.477 | Exit 0 | `leanchecker.exe` |
| `leanchecker.exe Init` (parallel replay) | Windows 11 | 49.011 | Exit 0 | `leanchecker.exe` |
| `leanchecker.exe Std` (parallel replay) | Windows 11 | 84.019 | Exit 0 | `leanchecker.exe` |
| `leanchecker.exe --fresh Init` (full fresh replay) | Windows 11 | 150.365 | Exit 0 | `leanchecker.exe` |
| `leanchecker --fresh` (single `import Std` module) | WSL2 Linux | 214.960 | 953,308 KB (~931.0 MiB) max RSS | `/usr/bin/time -f` |
| Adversarial Lean fixtures (`9` cases) | Windows 11 | — | 9/9 rejected or flagged (`sorryAx` / `fakeUnsoundAxiom` / exit 1) | [run_adversarial.ps1](file:///c:/Users/devin/Desktop/lean/benchmarks/run_adversarial.ps1) |
