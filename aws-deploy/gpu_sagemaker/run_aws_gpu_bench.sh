#!/usr/bin/env bash
set -euo pipefail

export PATH="/opt/bench:${PATH}"
MODEL_DIR="/opt/ml/model"
CLOSURES_DIR="/opt/ml/input/data/closures"
mkdir -p "${MODEL_DIR}"

# ---------------------------------------------------------------------------
# 1. Configure NVIDIA Vulkan ICD strictly (never fall back to llvmpipe/Mesa)
# ---------------------------------------------------------------------------
ICD_DIR="/etc/vulkan/icd.d"
ICD_FILE="${ICD_DIR}/nvidia_icd.json"
mkdir -p "${ICD_DIR}"

detect_nvidia_vulkan_lib() {
  local cand
  for lib in libGLX_nvidia.so.0 libEGL_nvidia.so.0; do
    cand="$(ldconfig -p 2>/dev/null | awk -v name="${lib}" '$1 == name {print $NF; exit}')"
    if [[ -n "${cand}" && -e "${cand}" ]]; then
      echo "${cand}"
      return 0
    fi
    for dir in /usr/lib/x86_64-linux-gnu /usr/lib64 /lib/x86_64-linux-gnu; do
      if [[ -e "${dir}/${lib}" ]]; then
        echo "${dir}/${lib}"
        return 0
      fi
    done
  done
  return 1
}

if [[ ! -s "${ICD_FILE}" ]]; then
  if [[ -s /usr/share/vulkan/icd.d/nvidia_icd.json ]]; then
    cp /usr/share/vulkan/icd.d/nvidia_icd.json "${ICD_FILE}"
  else
    NV_LIB="$(detect_nvidia_vulkan_lib || true)"
    if [[ -z "${NV_LIB}" ]]; then
      echo "ERROR: Could not locate libGLX_nvidia.so.0 or libEGL_nvidia.so.0 for Vulkan ICD" >&2
      ldconfig -p >&2 || true
      exit 2
    fi
    cat > "${ICD_FILE}" <<EOF
{
    "file_format_version" : "1.0.0",
    "ICD": {
        "library_path": "${NV_LIB}",
        "api_version" : "1.3.0"
    }
}
EOF
  fi
fi

export VK_ICD_FILENAMES="${ICD_FILE}"
echo "Using VK_ICD_FILENAMES=${VK_ICD_FILENAMES}"
cat "${ICD_FILE}"

# ---------------------------------------------------------------------------
# 2. Capture host/GPU system telemetry & verify discrete NVIDIA GPU presence
# ---------------------------------------------------------------------------
SYSINFO_FILE="${MODEL_DIR}/gpu_sysinfo.txt"
{
  echo "=== TIMESTAMP ==="
  date -u +"%Y-%m-%dT%H:%M:%SZ"
  echo "=== LSCPU ==="
  lscpu || true
  echo "=== FREE -M ==="
  free -m || true
  echo "=== NVIDIA-SMI -L ==="
  nvidia-smi -L
  echo "=== NVIDIA-SMI -Q ==="
  nvidia-smi -q
  echo "=== VULKANINFO --SUMMARY ==="
  vulkaninfo --summary
} > "${SYSINFO_FILE}" 2>&1

if ! nvidia-smi -L | grep -qi "GPU"; then
  echo "ERROR: No NVIDIA GPU reported by nvidia-smi -L" >&2
  cat "${SYSINFO_FILE}" >&2
  exit 2
fi
if ! vulkaninfo --summary 2>&1 | grep -qiE "NVIDIA|GeForce|Tesla|A10G|L4|L40|H100|T4|V100"; then
  echo "ERROR: Discrete NVIDIA Vulkan physical device not found in vulkaninfo --summary" >&2
  cat "${SYSINFO_FILE}" >&2
  exit 2
fi

NPROC="$(nproc)"

# ---------------------------------------------------------------------------
# 3. Unpack bundled soundness fixtures & run con-gpu test-soundness (exit=0)
# ---------------------------------------------------------------------------
FIXTURES_TMP="/tmp/con_gpu_fixtures"
rm -rf "${FIXTURES_TMP}"
FIXTURES_TAR=""
for cand in \
  "/opt/bench/fixtures.tar.zst" \
  "/opt/ml/input/data/fixtures/fixtures.tar.zst" \
  "${CLOSURES_DIR}/fixtures.tar.zst"; do
  if [[ -f "${cand}" ]]; then
    FIXTURES_TAR="${cand}"
    break
  fi
done

SOUNDNESS_ARGS=()
if [[ -n "${FIXTURES_TAR}" ]]; then
  mkdir -p "${FIXTURES_TMP}"
  tar --use-compress-program=zstd -xf "${FIXTURES_TAR}" -C "${FIXTURES_TMP}"
  export CON_GPU_FIXTURES_DIR="${FIXTURES_TMP}"
  SOUNDNESS_ARGS=(--fixtures-dir "${FIXTURES_TMP}")
elif [[ -d /opt/bench/fixtures ]]; then
  export CON_GPU_FIXTURES_DIR="/opt/bench/fixtures"
  SOUNDNESS_ARGS=(--fixtures-dir /opt/bench/fixtures)
fi

echo "=== Running con-gpu test-soundness ==="
/opt/bench/con-gpu test-soundness "${SOUNDNESS_ARGS[@]}" 2>&1 | tee "${MODEL_DIR}/test_soundness.log"
SOUNDNESS_RC="${PIPESTATUS[0]}"
rm -rf "${FIXTURES_TMP}"
if [[ "${SOUNDNESS_RC}" -ne 0 ]]; then
  echo "ERROR: con-gpu test-soundness exited ${SOUNDNESS_RC}" >&2
  exit "${SOUNDNESS_RC}"
fi

# ---------------------------------------------------------------------------
# 4. Synthetic Pipeline B + Pipeline C scaling benchmark
# ---------------------------------------------------------------------------
echo "=== Running con-gpu bench-synthetic (threads=${NPROC}) ==="
/opt/bench/con-gpu bench-synthetic \
  --threads "${NPROC}" \
  --backend both \
  --json-out "${MODEL_DIR}/bench_synthetic.json"

# ---------------------------------------------------------------------------
# 5. Iterate over every *.tar.zst .olean closure under /opt/ml/input/data/closures/
# ---------------------------------------------------------------------------
if [[ -d "${CLOSURES_DIR}" ]]; then
  shopt -s nullglob
  for archive in "${CLOSURES_DIR}"/*.tar.zst; do
    base="$(basename "${archive}" .tar.zst)"
    if [[ "${base}" == "fixtures" ]]; then
      continue
    fi
    work_dir="/tmp/closure_${base}"
    snap_file="/tmp/${base}.cgsnap"
    rm -rf "${work_dir}" "${snap_file}"
    mkdir -p "${work_dir}"

    echo "=== Processing closure ${base} (${archive}) ==="
    tar --use-compress-program=zstd -xf "${archive}" -C "${work_dir}"

    MANIFEST="$(find "${work_dir}" -maxdepth 3 -name manifest.env -print -quit || true)"
    if [[ -z "${MANIFEST}" ]]; then
      echo "ERROR: manifest.env missing in ${archive}" >&2
      rm -rf "${work_dir}" "${snap_file}"
      exit 2
    fi

    # Resolve LOAD_PATHS and ROOT_OLEANS relative to manifest directory cleanly
    MANIFEST_DIR="$(dirname "${MANIFEST}")"
    RESOLVED="$(python3 - "${MANIFEST}" "${MANIFEST_DIR}" <<'PY'
import os, shlex, sys

manifest_path, root_dir = sys.argv[1], sys.argv[2]
vals = {}
with open(manifest_path, "r", encoding="utf-8") as f:
    for line in f:
        s = line.strip()
        if not s or s.startswith("#") or "=" not in s:
            continue
        k, v = s.split("=", 1)
        k = k.strip()
        v = v.strip()
        if len(v) >= 2 and v[0] == v[-1] and v[0] in ('"', "'"):
            v = v[1:-1]
        vals[k] = v

def split_items(raw):
    if not raw:
        return []
    out = []
    for part in raw.replace(";", ":").split(":"):
        for tok in shlex.split(part):
            if tok:
                out.append(tok)
    return out

def resolve_rel(items):
    res = []
    for item in items:
        if os.path.isabs(item):
            res.append(item)
        else:
            res.append(os.path.normpath(os.path.join(root_dir, item)))
    return res

load_paths = ";".join(resolve_rel(split_items(vals.get("LOAD_PATHS", ""))))
root_oleans = resolve_rel(split_items(vals.get("ROOT_OLEANS", "")))
if not root_oleans:
    raise SystemExit("ROOT_OLEANS missing in manifest.env")
print(load_paths)
for r in root_oleans:
    print(r)
PY
)"
    LOAD_PATHS_ARG="$(printf '%s\n' "${RESOLVED}" | sed -n '1p')"
    mapfile -t ROOT_OLEAN_ARGS < <(printf '%s\n' "${RESOLVED}" | sed -n '2,$p')

    EXTRA_LP=()
    if [[ -n "${LOAD_PATHS_ARG}" ]]; then
      EXTRA_LP=(--load-paths "${LOAD_PATHS_ARG}")
    fi

    echo "--- [${base}] 1/3 Cold hybrid + --save-snapshot ---"
    /opt/bench/con-gpu verify --fresh --backend hybrid --jobs "${NPROC}" \
      --trust-bv-decide-axioms \
      --save-snapshot "${snap_file}" \
      --json-out "${MODEL_DIR}/${base}_hybrid_cold.json" \
      "${EXTRA_LP[@]}" "${ROOT_OLEAN_ARGS[@]}"

    echo "--- [${base}] 2/3 Warm CGSNAP03 hybrid --snapshot ---"
    /opt/bench/con-gpu verify --fresh --backend hybrid --jobs "${NPROC}" \
      --trust-bv-decide-axioms \
      --snapshot "${snap_file}" \
      --json-out "${MODEL_DIR}/${base}_hybrid_snap.json" \
      "${EXTRA_LP[@]}" "${ROOT_OLEAN_ARGS[@]}"

    echo "--- [${base}] 3/3 Warm CGSNAP03 cpu --snapshot ---"
    /opt/bench/con-gpu verify --fresh --backend cpu --jobs "${NPROC}" \
      --trust-bv-decide-axioms \
      --snapshot "${snap_file}" \
      --json-out "${MODEL_DIR}/${base}_cpu_snap.json" \
      "${EXTRA_LP[@]}" "${ROOT_OLEAN_ARGS[@]}"

    case "${base}" in
      Mathlib_Real_Basic|Full_Mathlib)
        echo "--- [${base}] 4/4 Strict --verify-olean-hashes --snapshot ---"
        /opt/bench/con-gpu verify --fresh --backend hybrid --jobs "${NPROC}" \
          --trust-bv-decide-axioms \
          --verify-olean-hashes \
          --snapshot "${snap_file}" \
          --json-out "${MODEL_DIR}/${base}_hybrid_hashcheck.json" \
          "${EXTRA_LP[@]}" "${ROOT_OLEAN_ARGS[@]}"
        ;;
    esac

    rm -rf "${work_dir}" "${snap_file}"
  done
fi

# ---------------------------------------------------------------------------
# 6. Emit SHA256 checksums for all artifacts in /opt/ml/model/
# ---------------------------------------------------------------------------
(
  cd "${MODEL_DIR}"
  rm -f sha256sums.txt
  find . -maxdepth 1 -type f ! -name 'sha256sums.txt' -printf '%f\n' | sort | xargs -r sha256sum > /tmp/sha256sums.txt
  mv /tmp/sha256sums.txt "${MODEL_DIR}/sha256sums.txt"
)
echo "=== SageMaker GPU Benchmark Complete ==="
