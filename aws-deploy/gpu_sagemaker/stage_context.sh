#!/usr/bin/env bash
set -euo pipefail

# Stage Linux release binaries + soundness fixtures into aws-deploy/gpu_sagemaker/
# for `docker build -t con-gpu-sagemaker:phase6 aws-deploy/gpu_sagemaker/`.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

CON_GPU_BIN="${1:-${REPO_ROOT}/con-gpu/target/release/con-gpu}"
LEANCHECKER_BIN="${2:-${HOME}/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanchecker}"

if [[ ! -x "${CON_GPU_BIN}" ]]; then
  echo "ERROR: Linux con-gpu binary not found or not executable: ${CON_GPU_BIN}" >&2
  exit 2
fi
if [[ ! -x "${LEANCHECKER_BIN}" ]]; then
  echo "ERROR: Linux leanchecker binary not found or not executable: ${LEANCHECKER_BIN}" >&2
  exit 2
fi

cp -f "${CON_GPU_BIN}" "${SCRIPT_DIR}/con-gpu"
# The released Linux checker loads these libraries through its relative RPATH.
stock_root="${SCRIPT_DIR}/stock"
mkdir -p "${stock_root}/bin" "${stock_root}/lib/lean"
cp -f "${LEANCHECKER_BIN}" "${stock_root}/bin/leanchecker"
checker_prefix="$(dirname "$(dirname "$(realpath "${LEANCHECKER_BIN}")")")"
for lib in libInit_shared.so libLake_shared.so libleanshared.so libleanshared_1.so libleanshared_2.so; do
  cp -L "${checker_prefix}/lib/lean/${lib}" "${stock_root}/lib/lean/${lib}"
done
cat > "${SCRIPT_DIR}/leanchecker" <<'CHECKER'
#!/usr/bin/env bash
set -euo pipefail
stock_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/stock" && pwd)"
export LEAN_SYSROOT="${LEAN_SYSROOT:-${stock_root}}"
exec "${stock_root}/bin/leanchecker" "$@"
CHECKER
chmod +x "${SCRIPT_DIR}/con-gpu" "${SCRIPT_DIR}/leanchecker" "${SCRIPT_DIR}/run_aws_gpu_bench.sh"

TMP_FIX="$(mktemp -d)"
trap 'rm -rf "${TMP_FIX}"' EXIT
mkdir -p "${TMP_FIX}/lrat_fixtures" "${TMP_FIX}/corrupt_oleans" "${TMP_FIX}/con-leche/tests"
cp -a "${REPO_ROOT}/benchmarks/lrat_fixtures/." "${TMP_FIX}/lrat_fixtures/"
cp -a "${REPO_ROOT}/benchmarks/corrupt_oleans/." "${TMP_FIX}/corrupt_oleans/"
cp -a "${REPO_ROOT}/vendor/con-leche/tests/e2e" "${TMP_FIX}/con-leche/tests/e2e"
cp -a "${REPO_ROOT}/vendor/con-leche/tests/e2e-expected.txt" "${TMP_FIX}/con-leche/tests/e2e-expected.txt"

tar --use-compress-program=zstd -cf "${SCRIPT_DIR}/fixtures.tar.zst" -C "${TMP_FIX}" .
ls -lh "${SCRIPT_DIR}/con-gpu" "${SCRIPT_DIR}/leanchecker" "${SCRIPT_DIR}/fixtures.tar.zst"
