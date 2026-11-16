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
if [[ -n "${EXPECTED_NVIDIA_GPU:-}" ]]; then
  sha256sum /opt/bench/con-gpu | awk '{ print $1 }' > "${MODEL_DIR}/con_gpu_binary.sha256"
fi

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
if [[ -n "${EXPECTED_NVIDIA_GPU:-}" ]]; then
  python3 /opt/bench/phase6_nvidia.py check-device "${EXPECTED_NVIDIA_GPU}" "${MODEL_DIR}/bench_synthetic.json"
fi

run_closure() {
    local base="$1" MANIFEST="$2" snap_file="/tmp/${1}.cgsnap"
    local MANIFEST_DIR RESOLVED EXPECTED_EXIT LOAD_PATHS_ARG RC_HYBRID RC_CPU result
    local -a ROOT_OLEAN_ARGS EXTRA_LP
    rm -f "${snap_file}"
  # Resolve EXPECTED_EXIT, LOAD_PATHS, and ROOT_OLEANS cleanly
    MANIFEST_DIR="$(dirname "${MANIFEST}")"
    RESOLVED="$(python3 - "${MANIFEST}" "${MANIFEST_DIR}" "${base}" <<'PY'
import os, shlex, sys

manifest_path, root_dir, base_name = sys.argv[1], sys.argv[2], sys.argv[3]
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

default_expected = "2" if base_name in ("Cedar", "PrimeNumberTheoremAnd") else "0"
expected_exit = vals.get("EXPECTED_EXIT", default_expected).strip() or default_expected
load_paths = ";".join(resolve_rel(split_items(vals.get("LOAD_PATHS", ""))))
root_oleans = resolve_rel(split_items(vals.get("ROOT_OLEANS", "")))
if not root_oleans:
    raise SystemExit("ROOT_OLEANS missing in manifest.env")
print(expected_exit)
print(load_paths)
for r in root_oleans:
    print(r)
PY
)"
    EXPECTED_EXIT="$(printf '%s\n' "${RESOLVED}" | sed -n '1p')"
    LOAD_PATHS_ARG="$(printf '%s\n' "${RESOLVED}" | sed -n '2p')"
    mapfile -t ROOT_OLEAN_ARGS < <(printf '%s\n' "${RESOLVED}" | sed -n '3,$p')

    EXTRA_LP=()
    if [[ -n "${LOAD_PATHS_ARG}" ]]; then
      EXTRA_LP=(--load-paths "${LOAD_PATHS_ARG}")
    fi

    echo "--- [${base}] 1/3 Cold hybrid + --save-snapshot (expected_exit=${EXPECTED_EXIT}) ---"
    set +e
    /opt/bench/con-gpu verify --fresh --backend hybrid --jobs "${NPROC}" \
      --trust-bv-decide-axioms \
      --save-snapshot "${snap_file}" \
      --json-out "${MODEL_DIR}/${base}_hybrid_cold.json" \
      "${EXTRA_LP[@]}" "${ROOT_OLEAN_ARGS[@]}" 2>&1 | tee "${MODEL_DIR}/${base}_hybrid_cold.log"
    RC_HYBRID=${PIPESTATUS[0]}
    set -e
    if [[ "${RC_HYBRID}" -ne "${EXPECTED_EXIT}" ]]; then
      echo "ERROR: [${base}] hybrid cold exited ${RC_HYBRID}, expected ${EXPECTED_EXIT}" >&2
      rm -rf "${work_dir}" "${snap_file}"
      exit 2
    fi

    if [[ "${EXPECTED_EXIT}" -eq 0 ]]; then
      if [[ ! -s "${snap_file}" ]]; then
        echo "ERROR: [${base}] accepted closure did not produce a snapshot" >&2
        return 1
      fi
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

      if [[ "${RUN_CPU_COLD:-0}" == "1" ]]; then
        echo "--- [${base}] Cold cpu (RUN_CPU_COLD=1) ---"
        /opt/bench/con-gpu verify --fresh --backend cpu --jobs "${NPROC}" \
          --trust-bv-decide-axioms \
          --json-out "${MODEL_DIR}/${base}_cpu_cold.json" \
          "${EXTRA_LP[@]}" "${ROOT_OLEAN_ARGS[@]}"
      fi

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
    else
      echo "--- [${base}] Expected Declined (exit=${EXPECTED_EXIT}); running CPU cold differential check ---"
      set +e
      /opt/bench/con-gpu verify --fresh --backend cpu --jobs "${NPROC}" \
        --trust-bv-decide-axioms \
        --json-out "${MODEL_DIR}/${base}_cpu_cold.json" \
        "${EXTRA_LP[@]}" "${ROOT_OLEAN_ARGS[@]}" 2>&1 | tee "${MODEL_DIR}/${base}_cpu_cold.log"
      RC_CPU=${PIPESTATUS[0]}
      set -e
      if [[ "${RC_CPU}" -ne "${EXPECTED_EXIT}" ]]; then
        echo "ERROR: [${base}] cpu cold exited ${RC_CPU}, expected ${EXPECTED_EXIT}" >&2
        rm -rf "${work_dir}" "${snap_file}"
        exit 2
      fi
    fi


    if [[ -n "${EXPECTED_NVIDIA_GPU:-}" ]]; then
      for result in "${MODEL_DIR}/${base}"_hybrid_*.json; do
        python3 /opt/bench/phase6_nvidia.py check-device "${EXPECTED_NVIDIA_GPU}" "${result}"
      done
    fi
    rm -f "${snap_file}"
}

processed=0
scope="${PHASE6_PACKAGE_SCOPE:-all}"
case "${scope}" in all|tails|supplement) ;; *) echo "ERROR: invalid PHASE6_PACKAGE_SCOPE=${scope}" >&2; exit 2 ;; esac

# A supplement omits libraries already present in the two-root archive.
# Load the base first even when this job only measures the supplement.
base_archive="${CLOSURES_DIR}/phase6_cpu_gpu_roots.tar.zst"
supplement_archive="${CLOSURES_DIR}/phase6_11_supplement.tar.zst"
shared_dir=""
base_sha=""
shopt -s nullglob
archives=()
if [[ -f "${base_archive}" ]]; then archives+=("${base_archive}"); fi
if [[ -f "${supplement_archive}" && "${scope}" != tails ]]; then
  if [[ ! -f "${base_archive}" ]]; then echo "ERROR: supplement needs two-root archive" >&2; exit 2; fi
  archives+=("${supplement_archive}")
fi
for archive in "${CLOSURES_DIR}"/*.tar.zst; do
  case "${archive}" in "${base_archive}"|"${supplement_archive}"|*/fixtures.tar.zst) continue ;; esac
  archives+=("${archive}")
done

for archive in "${archives[@]}"; do
  archive_name="$(basename "${archive}" .tar.zst)"
  if [[ "${archive}" == "${supplement_archive}" ]]; then
    work_dir="${shared_dir}"
    # The next archive may have its own SHA256SUMS file with the same name.
    rm -f "${work_dir}/SHA256SUMS"
  else
    work_dir="$(mktemp -d /tmp/con-gpu-closure.XXXXXXXX)"
  fi
  tar --use-compress-program=zstd -xf "${archive}" -C "${work_dir}"
  archive_sha="$(sha256sum "${archive}" | cut -d' ' -f1)"
  if [[ -f "${work_dir}/SHA256SUMS" ]]; then
    (cd "${work_dir}" && sha256sum --quiet -c SHA256SUMS)
  fi
  if [[ "${archive}" == "${base_archive}" ]]; then
    shared_dir="${work_dir}"
    base_sha="${archive_sha}"
  fi
  mapfile -d '' -t manifests < <(find "${work_dir}" -maxdepth 3 -type f -name manifest.env -print0 | sort -z)
  if [[ "${#manifests[@]}" -eq 0 ]]; then
    echo "ERROR: no manifest.env in ${archive}" >&2
    exit 1
  fi
  for manifest in "${manifests[@]}"; do
    base="${archive_name}"
    if [[ "${#manifests[@]}" -gt 1 || -f "${work_dir}/inputs.json" ]]; then
      base="$(basename "$(dirname "${manifest}")")"
    fi
    case "${base}" in
      Full_Mathlib|PrimeNumberTheoremAnd)
        if [[ "${scope}" == supplement || "${archive}" == "${supplement_archive}" ]]; then continue; fi ;;
      *) if [[ "${scope}" == tails ]]; then continue; fi ;;
    esac
    if [[ ! "${base}" =~ ^[A-Za-z0-9_]+$ || -e "${MODEL_DIR}/${base}_archive.sha256" ]]; then
      echo "ERROR: invalid or duplicate package '${base}'" >&2
      exit 1
    fi
    printf '%s  %s\n' "${archive_sha}" "$(basename "${archive}")" > "${MODEL_DIR}/${base}_archive.sha256"
    if [[ "${archive}" == "${supplement_archive}" ]]; then
      printf '%s  %s\n' "${base_sha}" "$(basename "${base_archive}")" > "${MODEL_DIR}/${base}_base_archive.sha256"
    fi
    run_closure "${base}" "${manifest}"
    processed=$((processed + 1))
  done
  if [[ "${archive}" != "${base_archive}" || ! -f "${supplement_archive}" || "${scope}" == tails ]]; then
    rm -rf "${work_dir}"
  fi
done
if [[ "${processed}" -eq 0 ]]; then
  echo "ERROR: no closure benchmarks ran" >&2
  exit 1
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
