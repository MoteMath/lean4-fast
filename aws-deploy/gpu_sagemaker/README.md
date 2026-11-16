# `con-gpu` AWS SageMaker NVIDIA Vulkan Benchmark Container (`gpu_sagemaker`)

Zero-floating-point GPU Vulkan + multi-core `rayon` benchmark container kit for AWS SageMaker Processing (`ml.g5.*`, `ml.g6.*`, `ml.p4d.*`, etc.).

## Files

- [`Dockerfile`](Dockerfile): `ubuntu:24.04` image with `NVIDIA_VISIBLE_DEVICES=all`, `NVIDIA_DRIVER_CAPABILITIES=all`, Vulkan loader (`libvulkan1`, `vulkan-tools`, `libglvnd0`, `libglx0`, `libegl1`), compression tools (`zstd`, `tar`), and **zero `mesa-vulkan-drivers`** so Vulkan binds strictly to the discrete NVIDIA ICD.
- [`run_aws_gpu_bench.sh`](run_aws_gpu_bench.sh): Entrypoint script that configures `/etc/vulkan/icd.d/nvidia_icd.json` (`VK_ICD_FILENAMES`), captures hardware/driver info to `/opt/ml/model/gpu_sysinfo.txt`, runs `con-gpu test-soundness` and `con-gpu bench-synthetic --backend both`, iterates through every `*.tar.zst` `.olean` closure under `/opt/ml/input/data/closures/` (reading `manifest.env` for `ROOT_OLEANS` and `LOAD_PATHS`, running cold hybrid `--save-snapshot`, warm `CGSNAP03` hybrid `--snapshot`, warm `CGSNAP03` CPU `--snapshot`, plus `--verify-olean-hashes` on `Mathlib_Real_Basic` / `Full_Mathlib`), cleans `/tmp/closure_*` and `/tmp/*.cgsnap` immediately after each closure, and writes `/opt/ml/model/sha256sums.txt`.
- [`stage_context.sh`](stage_context.sh): Stages Linux `con-gpu`, `leanchecker`, and bundled `fixtures.tar.zst` (`lrat_fixtures`, `corrupt_oleans`, and `con-leche/tests/{e2e,e2e-expected.txt}`) into the Docker build context.

## Build Example (Linux / WSL2 Host)

```bash
./aws-deploy/gpu_sagemaker/stage_context.sh /path/to/con-gpu /path/to/leanchecker
docker build -t con-gpu-sagemaker:phase5 aws-deploy/gpu_sagemaker
```
