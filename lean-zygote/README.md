# lean-zygote: Linux Copy-On-Write Persistent Import Fork-Server

Eliminates redundant N x 2-3 GB `importModules` / `finalizeImport` RAM and C++ / runtime startup overhead in parallel Lean 4 builds (such as 96-vCPU / 128 GB AWS formalization instances and heterogeneous shaken-import builds).

## Architecture

1. **`lean-zygote`** (daemon):
   - Initializes the Lean runtime with `LEAN_NUM_THREADS=1` (`lean_initialize()`, `initialize_LeanZygoteShim(1)`, `lean_io_mark_end_initialization()`, `lean_before_fork_stop_workers()`).
   - **Clean-Runtime CoW Helper (`--fork-any`)**: Before calling `Lean.importModules`, if `--fork-any` is passed, `lean-zygote` creates an `AF_UNIX` `socketpair` and forks a lightweight clean-runtime CoW helper process holding only the initialized runtime (`libInit_shared`, `libleanshared`, mimalloc, C++ initializers) with zero preloaded `.olean` snapshots.
   - **Process-Isolated Multi-Snapshot CoW Pool (`--profile`, `--import`, `--imports-from`, `--setup`)**: When multiple profiles are specified, `lean-zygote` forks isolated helper processes (`snap_helpers[1..K-1]`) from the clean initialized runtime *before* loading `profiles[0]` in the main daemon. Each profile preloads independently into a persistent `ZygoteSnapshot` (`Runtime.markPersistent`, `m_rc == 0`) without cross-contaminating `[init]` global state or `EnvExtension` indices across profiles, stops background worker threads, and returns serialized `ZygoteSnapshotMeta` metadata (`lean_zygote_snapshot_meta_json`) to the coordinator.
   - Listens on a Unix domain socket (`LEAN_ZYGOTE_SOCK`, default `/tmp/lean-zygote.sock`).
   - On each compile request from `lean-zygote-client`:
     - Calls `lean_zygote_select_snapshot_meta`: checks `trustLevel`, empty `dynlibs`/`plugins`, `isModule`, `imports`, `directRoots`, and `loadedOLeans` mtime/realpath parity across the pool's `ZygoteSnapshotMeta` array.
     - **Snapshot CoW hit**: if profile `0` matches, the main daemon forks directly; if profile `i >= 1` matches, it forwards `(conn_fd, stdout_fd, stderr_fd)` via `SCM_RIGHTS` to `snap_helpers[i]`, which forks from its isolated CoW snapshot. The child restarts `task_manager` (`lean_after_fork_restart_workers`), injects the CoW persistent `Environment` via `Elab.setPreloadedImportHook`, elaborates the module into `.olean` / `.ilean` / `.c` outputs with 0 RC dirty faults on shared persistent pages, streams exact diagnostics, and `_exit()`s.
     - **Snapshot miss + `--fork-any` (`lean_zygote_can_run_clean == 1`)**: forwards `(conn_fd, stdout_fd, stderr_fd)` via `SCM_RIGHTS` and request metadata over the `socketpair` to the clean-runtime CoW helper, which forks a clean worker executing `Elab.runFrontend` directly (no preloaded hook) + `Compiler.LCNF.emitC` — avoiding cold dynamic linker / runtime startup with zero `execve` fallback.
     - **Unsupported flags / `dynlibs` / `plugins` (or `--no-fork-any`)**: responds `'F'` without forking so `lean-zygote-client` immediately `execvp`s `LEAN_BIN`.
   - Prints `lean-zygote: shutdown stats snapshot_hits=... clean_cow_hits=... fallbacks=...` on clean `SIGTERM` / `SIGINT`.

2. **`lean-zygote-client`** (drop-in `lean` compiler wrapper):
   - Tiny pure-POSIX C++ binary (< 0.5 ms cold start, no `libleanshared.so` load).
   - Used automatically by `lake build --zygote` or `LAKE_LEAN_WRAPPER=lean-zygote-client`.
   - Seamlessly falls back to `LEAN_BIN` whenever the daemon is unreachable, disabled (`LEAN_ZYGOTE_DISABLE=1`), or declines a request.

## Building (WSL2 / Linux)

```bash
make LEAN_BUILD_DIR=/home/devin/build-lean4-s2
make LEAN_BUILD_DIR=/home/devin/build-lean4-s2 install
```

## Usage

```bash
# Multi-snapshot pool (non-module Init + module MyProj.Base) + universal clean-runtime CoW (--fork-any):
lean-zygote \
  --profile Init \
  --profile module:MyProj.Base \
  --fork-any \
  --socket /tmp/lean-zygote.sock &

# Pure clean-runtime CoW daemon (zero snapshot preload) for shaken-import DAGs:
lean-zygote --no-preload --fork-any --socket /tmp/lean-zygote.sock &

# Drive parallel Lake build with CoW fork-server + RAM-aware concurrency cap
LEAN_ZYGOTE_SOCK=/tmp/lean-zygote.sock \
  lake build --zygote -j 96 --max-memory-mb auto
```
