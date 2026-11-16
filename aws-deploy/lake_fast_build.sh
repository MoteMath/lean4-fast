#!/usr/bin/env bash
set -euo pipefail

# Production runner for downstream Lean 4 builds on 96-vCPU / 128 GB AWS nodes.
# Starts lean-zygote (CoW persistent import fork-server) and optional con-gpu
# daemon (GPU Vulkan or CPU-SIMD), invokes Lake with RAM-aware concurrency
# throttling, flushes queued verification batches, and cleans up gracefully.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

PROJECT_DIR="."
PREBUILD_TARGET=""
BUILD_TARGET=""
IMPORT_SPEC=""
IMPORTS_FROM=""
SETUP_JSON=""
PROFILES=()
IS_MODULE=0
FORK_ANY=1
JOBS="$(nproc)"
MAX_MEMORY_MB="auto"
LEAN_THREADS="${LEAN_NUM_THREADS:-}"
USE_ZYGOTE=1
VERIFY_CON_GPU=0
CON_GPU_MODE="gpu"
CON_GPU_PORT="${CON_GPU_PORT:-47831}"
CON_GPU_BASE_OLEAN=""
BIN_DIR="${LEAN_BIN_DIR:-}"
SOCK_PATH="/tmp/lean-zygote-$$.sock"
DAEMON_PID=""
CON_GPU_DAEMON_PID=""
CON_GPU_DAEMON_LOG=""
CON_GPU_ADDR=""
CON_GPU_BIN_RESOLVED=""

usage() {
  cat <<EOF
Usage: $0 [OPTIONS] [-- extra lake build args...]
Options:
  --project <dir>              Project directory containing lakefile (default: .)
  --prebuild <target>          Build umbrella/base module first with regular Lake before starting daemon
  --target <target>            Target to build with Lake (default: package default)
  --import <Mod1,Mod2>         Comma-separated modules to preload into lean-zygote
  --imports-from <file>        Template .lean file whose header imports are preloaded into lean-zygote
  --setup <file.json>          Lake .setup.json to preload into lean-zygote
  --profile <spec>             Repeatable snapshot profile (<Mod1,Mod2>, module:<Mod>, setup:<json>, none)
  --module                     Preload snapshot in module (.exported) mode
  --fork-any                   Enable clean-runtime CoW helper for unmatched imports (default: enabled)
  --no-fork-any                Disable clean-runtime CoW helper (fall back to cold lean on snapshot miss)
  --jobs, -j <N>               Max concurrent Lake module jobs (default: nproc=$JOBS)
  --max-memory-mb <M|auto>     Lake RAM cap in MB or 'auto' (default: auto)
  --lean-threads <N>           Child LEAN_NUM_THREADS (default: 2 if jobs>=32 else 4; 0 for hw concurrency)
  --no-zygote                  Disable CoW fork-server (cold spawn throttled strictly by --max-memory-mb)
  --verify-con-gpu[=gpu|cpu]   Verify bv_decide LRAT proofs & emitted .oleans via con-gpu daemon (default mode: gpu)
  --con-gpu-base-olean <path>  Preload and verify base .olean/module into con-gpu daemon prefix cache
  --con-gpu-port <port>        TCP port for local con-gpu daemon (default: $CON_GPU_PORT)
  --bin-dir <dir>              Directory containing optimized lean/lake/lean-zygote/con-gpu binaries
EOF
}

EXTRA_ARGS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --project)        PROJECT_DIR="$2"; shift 2 ;;
    --prebuild)       PREBUILD_TARGET="$2"; shift 2 ;;
    --target)         BUILD_TARGET="$2"; shift 2 ;;
    --import)         IMPORT_SPEC="$2"; shift 2 ;;
    --imports-from)   IMPORTS_FROM="$2"; shift 2 ;;
    --setup)          SETUP_JSON="$2"; shift 2 ;;
    --profile)        PROFILES+=("$2"); shift 2 ;;
    --profile=*)      PROFILES+=("${1#--profile=}"); shift ;;
    --module)         IS_MODULE=1; shift ;;
    --fork-any)       FORK_ANY=1; shift ;;
    --no-fork-any)    FORK_ANY=0; shift ;;
    -j|--jobs)        JOBS="$2"; shift 2 ;;
    --max-memory-mb)  MAX_MEMORY_MB="$2"; shift 2 ;;
    --lean-threads)   LEAN_THREADS="$2"; shift 2 ;;
    --no-zygote)      USE_ZYGOTE=0; shift ;;
    --verify-con-gpu=*)
      VERIFY_CON_GPU=1
      CON_GPU_MODE="${1#--verify-con-gpu=}"
      shift
      ;;
    --verify-con-gpu)
      VERIFY_CON_GPU=1
      if [[ $# -ge 2 && ( "$2" == "gpu" || "$2" == "cpu" ) ]]; then
        CON_GPU_MODE="$2"
        shift 2
      else
        CON_GPU_MODE="gpu"
        shift
      fi
      ;;
    --con-gpu-base-olean) CON_GPU_BASE_OLEAN="$2"; shift 2 ;;
    --con-gpu-port)   CON_GPU_PORT="$2"; shift 2 ;;
    --bin-dir)        BIN_DIR="$2"; shift 2 ;;
    -h|--help)        usage; exit 0 ;;
    --)               shift; EXTRA_ARGS+=("$@"); break ;;
    *)                EXTRA_ARGS+=("$1"); shift ;;
  esac
done

case "$CON_GPU_MODE" in
  gpu|cpu) ;;
  *)
    echo "ERROR: Invalid --verify-con-gpu mode '$CON_GPU_MODE' (expected 'gpu' or 'cpu')" >&2
    exit 2
    ;;
esac

send_tcp_cmd() {
  local addr="$1"
  local payload="$2"
  local host="${addr%:*}"
  local port="${addr##*:}"
  if [[ "$CON_GPU_BIN_RESOLVED" == *.exe ]] && command -v powershell.exe >/dev/null 2>&1; then
    powershell.exe -NoProfile -NonInteractive -Command "\$c = New-Object System.Net.Sockets.TcpClient('$host', $port); \$s = \$c.GetStream(); \$s.ReadTimeout = 2000; \$w = New-Object System.IO.StreamWriter(\$s); \$r = New-Object System.IO.StreamReader(\$s); \$w.WriteLine('$payload'); \$w.Flush(); \$r.ReadLine(); \$c.Close()" </dev/null 2>/dev/null || return 1
  elif command -v python3 >/dev/null 2>&1; then
    python3 -c "import socket,sys; s=socket.create_connection((sys.argv[1],int(sys.argv[2])),timeout=2.0); s.sendall((sys.argv[3]+'\n').encode()); print(s.recv(4096).decode(errors='replace').strip()); s.close()" "$host" "$port" "$payload" 2>/dev/null || return 1
  else
    return 1
  fi
}

stop_zygote_daemon() {
  if [[ -n "$DAEMON_PID" ]] && kill -0 "$DAEMON_PID" 2>/dev/null; then
    kill -TERM "$DAEMON_PID" 2>/dev/null || true
    for _ in $(seq 1 40); do
      if ! kill -0 "$DAEMON_PID" 2>/dev/null; then
        break
      fi
      sleep 0.05
    done
    if kill -0 "$DAEMON_PID" 2>/dev/null; then
      kill -KILL "$DAEMON_PID" 2>/dev/null || true
    fi
    wait "$DAEMON_PID" 2>/dev/null || true
  fi
  DAEMON_PID=""
}

cleanup() {
  stop_zygote_daemon

  if [[ -n "$CON_GPU_DAEMON_PID" ]] && kill -0 "$CON_GPU_DAEMON_PID" 2>/dev/null; then
    if [[ -n "$CON_GPU_ADDR" ]]; then
      send_tcp_cmd "$CON_GPU_ADDR" "SHUTDOWN" >/dev/null 2>&1 || true
    fi
    for _ in $(seq 1 30); do
      if ! kill -0 "$CON_GPU_DAEMON_PID" 2>/dev/null; then
        break
      fi
      sleep 0.05
    done
    if kill -0 "$CON_GPU_DAEMON_PID" 2>/dev/null; then
      kill -TERM "$CON_GPU_DAEMON_PID" 2>/dev/null || true
      for _ in $(seq 1 30); do
        if ! kill -0 "$CON_GPU_DAEMON_PID" 2>/dev/null; then
          break
        fi
        sleep 0.05
      done
    fi
    if kill -0 "$CON_GPU_DAEMON_PID" 2>/dev/null; then
      kill -KILL "$CON_GPU_DAEMON_PID" 2>/dev/null || true
    fi
    wait "$CON_GPU_DAEMON_PID" 2>/dev/null || true
  fi

  rm -f "$SOCK_PATH"
  if [[ -n "$CON_GPU_DAEMON_LOG" ]]; then
    rm -f "$CON_GPU_DAEMON_LOG"
  fi
}
trap cleanup EXIT INT TERM

if [[ -z "$LEAN_THREADS" ]]; then
  if [[ "$JOBS" -ge 32 ]]; then
    LEAN_THREADS=2
  else
    LEAN_THREADS=4
  fi
fi

if [[ -z "$BIN_DIR" ]]; then
  if [[ -x "/home/devin/build-lean4-s2/bin/lean" ]]; then
    BIN_DIR="/home/devin/build-lean4-s2/bin"
  elif [[ -x "/opt/lean-opt/bin/lean" ]]; then
    BIN_DIR="/opt/lean-opt/bin"
  elif [[ -x "/home/devin/build-lean4-s1/bin/lean" ]]; then
    BIN_DIR="/home/devin/build-lean4-s1/bin"
  fi
fi

unset ELAN_TOOLCHAIN || true
CLEAN_PATH=""
IFS=':' read -ra PATH_PARTS <<< "${PATH:-}"
for p in "${PATH_PARTS[@]}"; do
  [[ -z "$p" ]] && continue
  case "$p" in
    */.elan/bin|*/.elan/bin/) continue ;;
  esac
  CLEAN_PATH="${CLEAN_PATH:+${CLEAN_PATH}:}${p}"
done
if [[ -n "$BIN_DIR" ]]; then
  export PATH="${BIN_DIR}${CLEAN_PATH:+:${CLEAN_PATH}}"
else
  export PATH="$CLEAN_PATH"
fi

LAKE_BIN="${LAKE_BIN:-$(command -v lake)}"
LEAN_BIN="${LEAN_BIN:-$(command -v lean)}"
ZYGOTE_BIN="${ZYGOTE_BIN:-$(command -v lean-zygote || true)}"
ZYGOTE_CLIENT_BIN="${ZYGOTE_CLIENT_BIN:-$(command -v lean-zygote-client || true)}"

resolve_con_gpu_bin() {
  if [[ -n "${CON_GPU_BIN:-}" ]] && [[ -x "${CON_GPU_BIN}" ]]; then
    echo "${CON_GPU_BIN}"
    return 0
  fi
  if command -v con-gpu >/dev/null 2>&1; then
    command -v con-gpu
    return 0
  fi
  local lean_dir lake_dir
  lean_dir="$(dirname "$LEAN_BIN")"
  lake_dir="$(dirname "$LAKE_BIN")"
  for cand in \
    "${lean_dir}/con-gpu" \
    "${lean_dir}/con-gpu.exe" \
    "${lake_dir}/con-gpu" \
    "${lake_dir}/con-gpu.exe" \
    "${REPO_ROOT}/con-gpu/target/release/con-gpu" \
    "${REPO_ROOT}/con-gpu/target/release/con-gpu.exe"; do
    if [[ -f "$cand" ]]; then
      echo "$cand"
      return 0
    fi
  done
  if command -v con-gpu.exe >/dev/null 2>&1; then
    command -v con-gpu.exe
    return 0
  fi
  return 1
}

to_con_gpu_path() {
  local p="$1"
  if [[ "$CON_GPU_BIN_RESOLVED" == *.exe && "$p" != /mnt/* ]] && command -v wslpath >/dev/null 2>&1; then
    wslpath -w "$p"
  else
    echo "$p"
  fi
}

cd "$PROJECT_DIR"
export LEAN_BIN

if [[ "$LEAN_THREADS" != "0" ]]; then
  export LEAN_NUM_THREADS="$LEAN_THREADS"
fi

# Warn if Linux overcommit is restricted on high-concurrency fork workloads
if [[ "$USE_ZYGOTE" -eq 1 && -r /proc/sys/vm/overcommit_memory ]]; then
  OC="$(cat /proc/sys/vm/overcommit_memory)"
  if [[ "$OC" == "2" ]]; then
    echo "WARNING: vm.overcommit_memory=2 may reject high-vCPU fork() CoW address spaces; consider sysctl -w vm.overcommit_memory=1" >&2
  fi
fi

if [[ -n "$PREBUILD_TARGET" ]]; then
  echo "[lake_fast_build] Prebuilding base target '$PREBUILD_TARGET' (-j $JOBS --max-memory-mb $MAX_MEMORY_MB)..."
  "$LAKE_BIN" build -j "$JOBS" --max-memory-mb "$MAX_MEMORY_MB" "$PREBUILD_TARGET"
fi

LAKE_FLAGS=(-j "$JOBS" --max-memory-mb "$MAX_MEMORY_MB")
WS_LEAN_PATH="$("$LAKE_BIN" env printenv LEAN_PATH 2>/dev/null || echo "${LEAN_PATH:-}")"

if [[ "$VERIFY_CON_GPU" -eq 1 ]]; then
  CON_GPU_BIN_RESOLVED="$(resolve_con_gpu_bin || true)"
  if [[ -z "$CON_GPU_BIN_RESOLVED" ]]; then
    echo "ERROR: --verify-con-gpu requested, but con-gpu / con-gpu.exe was not found (set CON_GPU_BIN or --bin-dir)" >&2
    exit 1
  fi

  CON_GPU_ADDR="127.0.0.1:${CON_GPU_PORT}"
  export LAKE_VERIFY_TRUST_BV_AX="${LAKE_VERIFY_TRUST_BV_AX:-1}"
  CON_GPU_DAEMON_ARGS=(daemon --addr "$CON_GPU_ADDR")
  if [[ "$CON_GPU_MODE" == "cpu" ]]; then
    CON_GPU_DAEMON_ARGS+=(--no-gpu)
    export CON_GPU_BACKEND="cpu"
  fi
  if [[ "$LAKE_VERIFY_TRUST_BV_AX" == "1" ]]; then
    CON_GPU_DAEMON_ARGS+=(--trust-bv-decide-axioms)
  fi
  if [[ -n "$CON_GPU_BASE_OLEAN" ]]; then
    BASE_ARG="$(to_con_gpu_path "$CON_GPU_BASE_OLEAN")"
    CON_GPU_DAEMON_ARGS+=(--base-olean "$BASE_ARG")
  fi

  CON_GPU_DAEMON_LOG="$(mktemp /tmp/con-gpu-daemon-XXXXXX.log)"
  echo "[lake_fast_build] Starting con-gpu daemon ($CON_GPU_ADDR, mode=$CON_GPU_MODE)..."
  LEAN_PATH="$WS_LEAN_PATH" "$CON_GPU_BIN_RESOLVED" "${CON_GPU_DAEMON_ARGS[@]}" </dev/null >"$CON_GPU_DAEMON_LOG" 2>&1 &
  CON_GPU_DAEMON_PID=$!

  export CON_GPU_BIN="$CON_GPU_BIN_RESOLVED"
  export LAKE_EXTERNAL_VERIFIER="$CON_GPU_BIN_RESOLVED"
  export CON_GPU_DAEMON_ADDR="$CON_GPU_ADDR"
  export CON_GPU_BATCH_QUEUE="${CON_GPU_BATCH_QUEUE:-1}"
  export LEAN_BV_DECIDE_CON_GPU="${LEAN_BV_DECIDE_CON_GPU:-1}"
  LAKE_FLAGS+=(--verify-with-con-gpu)
fi

if [[ "$USE_ZYGOTE" -eq 1 ]]; then
  if [[ -z "$ZYGOTE_BIN" || -z "$ZYGOTE_CLIENT_BIN" ]]; then
    echo "WARNING: lean-zygote / lean-zygote-client not found on PATH; running without CoW daemon." >&2
  else
    SYSROOT_DIR="$(cd "$(dirname "$LEAN_BIN")/.." && pwd)"
    DAEMON_ARGS=(--socket "$SOCK_PATH" --sysroot "$SYSROOT_DIR")
    [[ -n "$IMPORT_SPEC" ]]  && DAEMON_ARGS+=(--import "$IMPORT_SPEC")
    [[ -n "$IMPORTS_FROM" ]] && DAEMON_ARGS+=(--imports-from "$IMPORTS_FROM")
    [[ -n "$SETUP_JSON" ]]   && DAEMON_ARGS+=(--setup "$SETUP_JSON")
    if [[ ${#PROFILES[@]} -gt 0 ]]; then
      for prof in "${PROFILES[@]}"; do
        DAEMON_ARGS+=(--profile "$prof")
      done
    fi
    [[ "$IS_MODULE" -eq 1 ]] && DAEMON_ARGS+=(--module)
    [[ "$FORK_ANY" -eq 1 ]]  && DAEMON_ARGS+=(--fork-any)

    echo "[lake_fast_build] Starting lean-zygote CoW daemon ($SOCK_PATH)..."
    LEAN_PATH="$WS_LEAN_PATH" "$ZYGOTE_BIN" "${DAEMON_ARGS[@]}" &
    DAEMON_PID=$!

    export LEAN_ZYGOTE_SOCK="$SOCK_PATH"
    export LAKE_LEAN_WRAPPER="$ZYGOTE_CLIENT_BIN"
    LAKE_FLAGS+=(--zygote)
  fi
fi

if [[ -n "$CON_GPU_DAEMON_PID" ]]; then
  READY=0
  for _ in $(seq 1 1200); do
    if ! kill -0 "$CON_GPU_DAEMON_PID" 2>/dev/null; then
      echo "ERROR: con-gpu daemon exited prematurely:" >&2
      cat "$CON_GPU_DAEMON_LOG" >&2 || true
      exit 1
    fi
    if [[ "$CON_GPU_BIN_RESOLVED" == *.exe ]]; then
      if grep -q "listening on " "$CON_GPU_DAEMON_LOG" 2>/dev/null; then
        READY=1
        break
      fi
    else
      if PONG_RESP="$(send_tcp_cmd "$CON_GPU_ADDR" "PING" 2>/dev/null || true)" && [[ "$PONG_RESP" == PONG* ]]; then
        READY=1
        break
      fi
    fi
    sleep 0.05
  done
  if [[ "$READY" -ne 1 ]]; then
    echo "ERROR: Timed out waiting for con-gpu daemon readiness on $CON_GPU_ADDR" >&2
    cat "$CON_GPU_DAEMON_LOG" >&2 || true
    exit 1
  fi
  cat "$CON_GPU_DAEMON_LOG"
fi

if [[ -n "$DAEMON_PID" ]]; then
  for _ in $(seq 1 1200); do
    if [[ -S "$SOCK_PATH" ]]; then
      break
    fi
    if ! kill -0 "$DAEMON_PID" 2>/dev/null; then
      echo "ERROR: lean-zygote daemon exited prematurely" >&2
      exit 1
    fi
    sleep 0.05
  done
  if [[ ! -S "$SOCK_PATH" ]]; then
    echo "ERROR: Timed out waiting for lean-zygote socket $SOCK_PATH" >&2
    exit 1
  fi
fi

CMD=("$LAKE_BIN" build "${LAKE_FLAGS[@]}" ${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"})
[[ -n "$BUILD_TARGET" ]] && CMD+=("$BUILD_TARGET")

echo "[lake_fast_build] Executing: ${CMD[*]}"
"${CMD[@]}"
stop_zygote_daemon

if [[ "$VERIFY_CON_GPU" -eq 1 && "${CON_GPU_BATCH_QUEUE:-0}" == "1" ]]; then
  FLUSH_ARGS=(verify --daemon-addr "$CON_GPU_DAEMON_ADDR" --flush --backend "$CON_GPU_MODE")
  if [[ "${LAKE_VERIFY_TRUST_BV_AX:-1}" == "1" ]]; then
    FLUSH_ARGS+=(--trust-bv-decide-axioms)
  fi
  echo "[lake_fast_build] Flushing queued con-gpu verification batch..."
  set +e
  FLUSH_OUT="$("$CON_GPU_BIN_RESOLVED" "${FLUSH_ARGS[@]}" </dev/null 2>&1)"
  FLUSH_RC=$?
  set -e
  echo "$FLUSH_OUT"
  if [[ "$FLUSH_RC" -ne 0 ]]; then
    if [[ "$FLUSH_RC" -eq 2 && "${LAKE_VERIFY_STRICT:-0}" != "1" && "$FLUSH_OUT" == DECLINED* ]]; then
      echo "WARNING: con-gpu flush declined verification (LAKE_VERIFY_STRICT!=1); continuing." >&2
    else
      exit "$FLUSH_RC"
    fi
  fi
  if STATS_RESP="$(send_tcp_cmd "$CON_GPU_ADDR" "STATS" 2>/dev/null || true)" && [[ -n "$STATS_RESP" ]]; then
    echo "[lake_fast_build] $STATS_RESP"
  fi
fi
