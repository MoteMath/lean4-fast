#!/usr/bin/env bash
set -euo pipefail

# Verify 100% of emitted DownstreamBench .olean files using unmodified stock leanchecker --fresh
STOCK_TOOLCHAIN="${STOCK_TOOLCHAIN:-/home/devin/.elan/toolchains/leanprover--lean4---v4.35.0}"
LEANCHECKER="${STOCK_TOOLCHAIN}/bin/leanchecker"
PROJECT_DIR="${1:-}"
JOBS="${2:-8}"

if [[ -z "$PROJECT_DIR" || ! -d "$PROJECT_DIR/.lake/build/lib/lean" ]]; then
  echo "Usage: $0 <project-dir> [parallel-jobs]" >&2
  exit 2
fi

export LEAN_PATH="${PROJECT_DIR}/.lake/build/lib/lean:${STOCK_TOOLCHAIN}/lib/lean"
export LEANCHECKER

mapfile -t MODULES < <(
  cd "${PROJECT_DIR}/.lake/build/lib/lean"
  find DownstreamBench DownstreamBench.olean -maxdepth 4 -name '*.olean' 2>/dev/null \
    | sed 's/\.olean$//' | tr '/' '.' | sort -u
)

echo "Checking ${#MODULES[@]} emitted .olean modules with stock $LEANCHECKER --fresh (jobs=$JOBS)..."
t0=$(date +%s.%N)

printf '%s\n' "${MODULES[@]}" | xargs -P "$JOBS" -I {} bash -c '
  mod="$1"
  if "$LEANCHECKER" --fresh "$mod" >/tmp/lc_"${mod}".log 2>&1; then
    echo "  [OK] $mod"
    rm -f /tmp/lc_"${mod}".log
  else
    echo "  [FAIL] $mod" >&2
    cat /tmp/lc_"${mod}".log >&2
    rm -f /tmp/lc_"${mod}".log
    exit 1
  fi
' _ {}

t1=$(date +%s.%N)
python3 -c "print(f'All {${#MODULES[@]}} modules passed stock leanchecker --fresh in {${t1}-${t0}:.2f}s')"
