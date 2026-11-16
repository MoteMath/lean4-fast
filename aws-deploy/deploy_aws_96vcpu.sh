#!/usr/bin/env bash
set -euo pipefail

# Provision & build the optimized Lean 4 + Lake + lean-zygote toolchain (and
# optional con-gpu CPU-SIMD/Vulkan verifier) on a 96-vCPU / 128 GB AWS instance
# (Ubuntu 22.04/24.04 or Amazon Linux 2023).

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
if [[ -z "${LEAN4_SRC:-}" ]]; then
  if [[ -d "${REPO_ROOT}/lean4/src" ]]; then
    LEAN4_SRC="${REPO_ROOT}/lean4"
  else
    LEAN4_SRC="${REPO_ROOT}"
  fi
fi
ZYGOTE_SRC="${ZYGOTE_SRC:-${REPO_ROOT}/lean-zygote}"
CON_GPU_SRC="${CON_GPU_SRC:-${REPO_ROOT}/con-gpu}"
BUILD_DIR="${BUILD_DIR:-/opt/lean-opt-build}"
INSTALL_DIR="${INSTALL_DIR:-/opt/lean-opt}"
PREV_STAGE="${PREV_STAGE:-}"
SKIP_STAGE2=0
APPLY_SYSCTL=0
SKIP_DEPS=0
NATIVE_CPU=0
BUILD_CON_GPU="auto" # auto | always | skip

while [[ $# -gt 0 ]]; do
  case "$1" in
    --install-dir) INSTALL_DIR="$2"; shift 2 ;;
    --build-dir)   BUILD_DIR="$2"; shift 2 ;;
    --prev-stage)  PREV_STAGE="$2"; shift 2 ;;
    --skip-stage2) SKIP_STAGE2=1; shift ;;
    --apply-sysctl) APPLY_SYSCTL=1; shift ;;
    --skip-deps)   SKIP_DEPS=1; shift ;;
    --native-cpu)  NATIVE_CPU=1; shift ;;
    --build-con-gpu) BUILD_CON_GPU="always"; shift ;;
    --skip-con-gpu)  BUILD_CON_GPU="skip"; shift ;;
    -h|--help)
      cat <<EOF
Usage: $0 [OPTIONS]
Options:
  --install-dir <dir>   Target prefix for bin/lib (default: /opt/lean-opt)
  --build-dir <dir>     CMake build directory for stage1/stage2 (default: /opt/lean-opt-build)
  --prev-stage <dir>    Stage0 Lean v4.35.0 toolchain root (default: ~/.elan/toolchains/leanprover--lean4---v4.35.0)
  --skip-stage2         Build and install Stage 1 only (default builds self-hosted Stage 2)
  --apply-sysctl        Apply recommended vm.overcommit_memory=1 & vm.max_map_count sysctls (requires sudo)
  --skip-deps           Skip OS package installation
  --native-cpu          Optimize Lean & cadical for host CPU (-march=native; user :c.o flags stay portable -O3)
  --build-con-gpu       Require & build con-gpu verifier (auto-installs minimal rustup if cargo missing)
  --skip-con-gpu        Skip building con-gpu even if cargo is available
EOF
      exit 0
      ;;
    *) echo "Unknown argument: $1" >&2; exit 1 ;;
  esac
done

echo "=== AWS 96-vCPU / 128 GB Lean 4 + Lake + lean-zygote Deployment ==="
echo "CPUs: $(nproc) | MemAvailable: $(awk '/MemAvailable/{printf "%.1f GB", $2/1024/1024}' /proc/meminfo)"

if [[ "$SKIP_DEPS" -eq 0 ]]; then
  if [[ -f /etc/os-release ]]; then
    # shellcheck disable=SC1091
    . /etc/os-release
  fi
  SUDO=""
  if [[ "$(id -u)" -ne 0 ]]; then
    SUDO="sudo"
  fi
  case "${ID:-unknown}" in
    ubuntu|debian)
      $SUDO apt-get update
      $SUDO apt-get install -y --no-install-recommends \
        git cmake ninja-build clang lld gcc g++ ccache make pkg-config \
        libgmp-dev libuv1-dev zlib1g-dev libssl-dev curl ca-certificates python3 numactl
      ;;
    amzn|rhel|fedora|centos|rocky|almalinux)
      $SUDO dnf install -y \
        git cmake ninja-build clang lld gcc gcc-c++ ccache make pkgconf-pkg-config \
        gmp-devel libuv-devel zlib-devel openssl-devel curl ca-certificates python3 numactl
      ;;
    *)
      echo "WARNING: Unrecognized distro '${ID:-unknown}', assuming build dependencies are installed." >&2
      ;;
  esac
fi

if [[ "$APPLY_SYSCTL" -eq 1 ]]; then
  SUDO=""
  [[ "$(id -u)" -ne 0 ]] && SUDO="sudo"
  echo "Applying Linux CoW / 96-vCPU kernel parameters..."
  $SUDO tee /etc/sysctl.d/99-lean-96vcpu.conf >/dev/null <<'SYSCTL'
# Allow safe Copy-On-Write fork() reservations across 96 parallel Lean workers
vm.overcommit_memory = 1
# Support many concurrent mimalloc arenas & compacted .olean regions
vm.max_map_count = 1048576
SYSCTL
  $SUDO sysctl --system >/dev/null
  $SUDO tee /etc/security/limits.d/99-lean-96vcpu.conf >/dev/null <<'LIMITS'
* soft nofile 65536
* hard nofile 65536
LIMITS
fi

if [[ -z "$PREV_STAGE" ]]; then
  ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
  if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
    echo "Installing elan + Lean v4.35.0 stage0 toolchain..."
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
      sh -s -- -y --default-toolchain leanprover/lean4:v4.35.0
  fi
  export PATH="$ELAN_HOME/bin:$PATH"
  elan toolchain install leanprover/lean4:v4.35.0 >/dev/null 2>&1 || true
  PREV_STAGE="$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0"
fi

if [[ ! -x "$PREV_STAGE/bin/lean" ]]; then
  echo "ERROR: PREV_STAGE Lean binary not found at $PREV_STAGE/bin/lean" >&2
  exit 1
fi

ulimit -c 0 || true
SUDO=""
if [[ "$(id -u)" -ne 0 ]]; then
  SUDO="sudo"
fi
ensure_writable_dir() {
  local dir="$1"
  if mkdir -p "$dir" 2>/dev/null && [[ -w "$dir" ]]; then
    return 0
  fi
  if [[ -n "$SUDO" ]]; then
    $SUDO mkdir -p "$dir"
    $SUDO chown -R "$(id -u):$(id -g)" "$dir"
  else
    mkdir -p "$dir"
  fi
}

ensure_writable_dir "$BUILD_DIR"
ensure_writable_dir "$INSTALL_DIR"

MIMALLOC_SRC_DIR="$BUILD_DIR/mimalloc/src/mimalloc"
if [[ ! -f "$MIMALLOC_SRC_DIR/include/mimalloc.h" ]]; then
  echo "Fetching mimalloc (v3.4.5) into $MIMALLOC_SRC_DIR..."
  mkdir -p "$(dirname "$MIMALLOC_SRC_DIR")"
  git clone --depth 1 --branch v3.4.5 https://github.com/microsoft/mimalloc "$MIMALLOC_SRC_DIR"
fi

JOBS="$(nproc)"
STAGE1_DIR="$BUILD_DIR/stage1"
STAGE2_DIR="$BUILD_DIR/stage2"

CC_BIN="${CC:-}"
if [[ -z "$CC_BIN" ]]; then
  if command -v clang >/dev/null 2>&1; then
    CC_BIN="clang"
  else
    CC_BIN="cc"
  fi
fi
CXX_BIN="${CXX:-}"
if [[ -z "$CXX_BIN" ]]; then
  if command -v clang++ >/dev/null 2>&1; then
    CXX_BIN="clang++"
  else
    CXX_BIN="c++"
  fi
fi
HAS_LLD=0
if command -v lld >/dev/null 2>&1 || command -v ld.lld >/dev/null 2>&1; then
  HAS_LLD=1
fi
echo "Toolchain: CC=$CC_BIN | CXX=$CXX_BIN | lld=$HAS_LLD | native-cpu=$NATIVE_CPU"

CADICAL_BIN=""
if [[ "$NATIVE_CPU" -eq 0 ]] && [[ -x "$PREV_STAGE/bin/cadical" ]] && ! ldd "$PREV_STAGE/bin/cadical" 2>/dev/null | grep -qE 'not found|libc\+\+'; then
  CADICAL_BIN="$PREV_STAGE/bin/cadical"
fi
if [[ -z "$CADICAL_BIN" ]]; then
  CADICAL_SRC_DIR="$BUILD_DIR/cadical/src/cadical"
  CADICAL_BIN="$BUILD_DIR/cadical/cadical"
  if [[ ! -x "$CADICAL_BIN" ]]; then
    CADICAL_CXXFLAGS="-DNCLOSEFROM"
    [[ "$NATIVE_CPU" -eq 1 ]] && CADICAL_CXXFLAGS="$CADICAL_CXXFLAGS -march=native"
    echo "Building native cadical (rel-2.1.2) with CXX=$CXX_BIN (without external libc++.so dependency)..."
    mkdir -p "$(dirname "$CADICAL_SRC_DIR")"
    git clone --depth 1 --branch rel-2.1.2 https://github.com/arminbiere/cadical "$CADICAL_SRC_DIR"
    make -C "$CADICAL_SRC_DIR" -f "$LEAN4_SRC/src/cadical.mk" -j "$JOBS" CXX="$CXX_BIN" CXXFLAGS="$CADICAL_CXXFLAGS"
  fi
fi

COMMON_CMAKE_COMPILER_ARGS=(
  -DCMAKE_C_COMPILER="$CC_BIN"
  -DCMAKE_CXX_COMPILER="$CXX_BIN"
  -DLEANC_CC="$CC_BIN"
)
if [[ "$HAS_LLD" -eq 1 ]]; then
  COMMON_CMAKE_COMPILER_ARGS+=(
    -DCMAKE_EXE_LINKER_FLAGS=-fuse-ld=lld
    -DCMAKE_SHARED_LINKER_FLAGS=-fuse-ld=lld
    -DLEAN_EXTRA_LINKER_FLAGS=-fuse-ld=lld
  )
fi
if [[ "$NATIVE_CPU" -eq 1 ]]; then
  COMMON_CMAKE_COMPILER_ARGS+=(
    -DCMAKE_C_FLAGS=-march=native
    -DLEAN_EXTRA_CXX_FLAGS=-march=native
  )
fi

STAGE1_CMAKE_ARGS=(
  -B "$STAGE1_DIR"
  -S "$LEAN4_SRC/src"
  -G Ninja
  -DCMAKE_BUILD_TYPE=Release
  -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR"
  -DSTAGE=1
  -DPREV_STAGE="$PREV_STAGE"
  -DLLVM=OFF
  -DUSE_MIMALLOC=ON
  -DCHECK_OLEAN_VERSION=OFF
  "${COMMON_CMAKE_COMPILER_ARGS[@]}"
)
[[ -x "$CADICAL_BIN" ]] && STAGE1_CMAKE_ARGS+=(-DCADICAL="$CADICAL_BIN")
[[ -x "$PREV_STAGE/bin/leantar" ]] && STAGE1_CMAKE_ARGS+=(-DLEANTAR="$PREV_STAGE/bin/leantar")

echo "Configuring Lean 4 Stage 1 at $STAGE1_DIR (PREV_STAGE=$PREV_STAGE, jobs=$JOBS)..."
cmake "${STAGE1_CMAKE_ARGS[@]}"

echo "Building Lean 4 Stage 1 (ninja -j $JOBS)..."
ninja -C "$STAGE1_DIR" -j "$JOBS"

ACTIVE_BUILD_DIR="$STAGE1_DIR"
if [[ "$SKIP_STAGE2" -eq 0 ]]; then
  STAGE2_CMAKE_ARGS=(
    -B "$STAGE2_DIR"
    -S "$LEAN4_SRC/src"
    -G Ninja
    -DCMAKE_BUILD_TYPE=Release
    -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR"
    -DSTAGE=2
    -DPREV_STAGE="$STAGE1_DIR"
    -DLLVM=OFF
    -DUSE_MIMALLOC=ON
    -DCHECK_OLEAN_VERSION=OFF
    "${COMMON_CMAKE_COMPILER_ARGS[@]}"
  )
  if [[ -x "$STAGE1_DIR/bin/cadical" ]]; then
    STAGE2_CMAKE_ARGS+=(-DCADICAL="$STAGE1_DIR/bin/cadical")
  elif [[ -x "$CADICAL_BIN" ]]; then
    STAGE2_CMAKE_ARGS+=(-DCADICAL="$CADICAL_BIN")
  fi
  if [[ -x "$STAGE1_DIR/bin/leantar" ]]; then
    STAGE2_CMAKE_ARGS+=(-DLEANTAR="$STAGE1_DIR/bin/leantar")
  elif [[ -x "$PREV_STAGE/bin/leantar" ]]; then
    STAGE2_CMAKE_ARGS+=(-DLEANTAR="$PREV_STAGE/bin/leantar")
  fi

  echo "Configuring Self-Hosted Lean 4 Stage 2 at $STAGE2_DIR (PREV_STAGE=$STAGE1_DIR, jobs=$JOBS)..."
  cmake "${STAGE2_CMAKE_ARGS[@]}"

  echo "Staging C++ runtime archives (copy-leancpp) for Ninja Stage 2..."
  ninja -C "$STAGE2_DIR" copy-leancpp

  echo "Building Self-Hosted Lean 4 Stage 2 (ninja -j $JOBS)..."
  ninja -C "$STAGE2_DIR" -j "$JOBS"
  ACTIVE_BUILD_DIR="$STAGE2_DIR"
fi

echo "Installing artifacts from $ACTIVE_BUILD_DIR to $INSTALL_DIR..."
cmake --install "$ACTIVE_BUILD_DIR"

# Expose clang inside $INSTALL_DIR/bin so Lake's `leanCcExe sysroot` uses clang + internal lld flags
# for `:c.o`, `:shared`, and `:exe` targets instead of falling back to system `cc` (gcc/ld).
if [[ ! -x "$INSTALL_DIR/bin/clang" ]] && command -v "$CC_BIN" >/dev/null 2>&1; then
  RESOLVED_CC="$(command -v "$CC_BIN")"
  if [[ "$(basename "$RESOLVED_CC")" == *clang* ]]; then
    cat > "$INSTALL_DIR/bin/clang" <<EOF
#!/usr/bin/env bash
exec "$RESOLVED_CC" "\$@"
EOF
    chmod +x "$INSTALL_DIR/bin/clang"
  fi
fi

for req_bin in lean lake leanc leanir leanchecker; do
  if [[ ! -x "$INSTALL_DIR/bin/$req_bin" ]]; then
    echo "ERROR: Required installed binary missing or not executable: $INSTALL_DIR/bin/$req_bin" >&2
    exit 1
  fi
done
if [[ ! -f "$INSTALL_DIR/lib/lean/libleanshared.so" ]]; then
  echo "ERROR: Required shared library missing: $INSTALL_DIR/lib/lean/libleanshared.so" >&2
  exit 1
fi

echo "Building & installing lean-zygote + lean-zygote-client against $INSTALL_DIR..."
make -C "$ZYGOTE_SRC" LEAN_BUILD_DIR="$INSTALL_DIR" clean
make -C "$ZYGOTE_SRC" LEAN_BUILD_DIR="$INSTALL_DIR" -j "$JOBS"
make -C "$ZYGOTE_SRC" LEAN_BUILD_DIR="$INSTALL_DIR" install

if [[ "$BUILD_CON_GPU" != "skip" ]]; then
  if [[ -f "${CARGO_HOME:-$HOME/.cargo}/env" ]]; then
    # shellcheck disable=SC1091
    . "${CARGO_HOME:-$HOME/.cargo}/env"
  fi
  export PATH="${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
  if [[ ! -f "$CON_GPU_SRC/Cargo.toml" ]]; then
    if [[ "$BUILD_CON_GPU" == "always" ]]; then
      echo "ERROR: --build-con-gpu requested, but $CON_GPU_SRC/Cargo.toml not found" >&2
      exit 1
    fi
  else
    if ! command -v cargo >/dev/null 2>&1 && [[ "$BUILD_CON_GPU" == "always" ]]; then
      echo "cargo not found; installing minimal Rust toolchain via rustup..."
      curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --profile minimal -y
      if [[ -f "${CARGO_HOME:-$HOME/.cargo}/env" ]]; then
        # shellcheck disable=SC1091
        . "${CARGO_HOME:-$HOME/.cargo}/env"
      fi
      export PATH="${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
    fi
    if command -v cargo >/dev/null 2>&1; then
      echo "Building con-gpu verifier (CPU-SIMD + Vulkan support, -j $JOBS)..."
      CARGO_BUILD_JOBS="$JOBS" cargo build --manifest-path "$CON_GPU_SRC/Cargo.toml" --release -j "$JOBS"
      cp -f "$CON_GPU_SRC/target/release/con-gpu" "$INSTALL_DIR/bin/con-gpu"
      chmod +x "$INSTALL_DIR/bin/con-gpu"
    elif [[ "$BUILD_CON_GPU" == "always" ]]; then
      echo "ERROR: --build-con-gpu requested, but cargo installation failed" >&2
      exit 1
    fi
  fi
fi

echo
echo "=== Deployment Complete ==="
echo "Install prefix: $INSTALL_DIR"
echo "Active stage:   $([[ "$SKIP_STAGE2" -eq 0 ]] && echo "Stage 2 (self-hosted)" || echo "Stage 1")"
echo "Toolchain:      CC=$CC_BIN CXX=$CXX_BIN lld=$HAS_LLD native-cpu=$NATIVE_CPU"
echo "Add to PATH:    export PATH=\"$INSTALL_DIR/bin:\$PATH\""
"$INSTALL_DIR/bin/lean" --version
"$INSTALL_DIR/bin/lake" --version
echo "leanc cflags:   $("$INSTALL_DIR/bin/leanc" --print-cflags)"
ldd "$INSTALL_DIR/bin/lean" | grep -E 'stdc\+\+|c\+\+|not found' || true
if [[ -x "$INSTALL_DIR/bin/con-gpu" ]]; then
  "$INSTALL_DIR/bin/con-gpu" --help | head -n 1 || true
fi
