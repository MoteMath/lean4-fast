#!/usr/bin/env python3
"""
Linux WSL2 benchmark & memory profiler for DownstreamBench.
Samples /proc/<pid>/smaps_rollup and /proc/<pid>/stat across the full process tree
(plus optional lean-zygote daemon PIDs) at 50 ms intervals during `lake build`.
"""
import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path


def read_proc_children():
    """Return mapping parent_pid -> list of child_pids, and pid -> comm/cmdline."""
    children = {}
    comms = {}
    for entry in os.scandir("/proc"):
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        try:
            with open(f"/proc/{pid}/stat", "r", encoding="utf-8", errors="replace") as f:
                stat = f.read()
            rparen = stat.rfind(")")
            if rparen == -1:
                continue
            comm = stat[stat.find("(") + 1 : rparen]
            rest = stat[rparen + 2 :].split()
            ppid = int(rest[1])
            children.setdefault(ppid, []).append(pid)
            comms[pid] = comm
        except OSError:
            continue
    return children, comms


def collect_descendants(root_pid, children):
    out = []
    stack = [root_pid]
    seen = set()
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        out.append(p)
        for c in children.get(p, ()):
            stack.append(c)
    return out


def read_smaps_rollup(pid):
    """Parse /proc/<pid>/smaps_rollup in KiB."""
    try:
        with open(f"/proc/{pid}/smaps_rollup", "r", encoding="utf-8") as f:
            lines = f.readlines()
    except OSError:
        return None
    metrics = {}
    for line in lines[1:]:
        parts = line.split()
        if len(parts) >= 2 and parts[0].endswith(":"):
            key = parts[0][:-1]
            try:
                metrics[key] = int(parts[1])
            except ValueError:
                pass
    return metrics


def read_cmdline(pid):
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as f:
            raw = f.read().replace(b"\x00", b" ").decode("utf-8", errors="replace").strip()
        return raw
    except OSError:
        return ""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workdir", required=True)
    parser.add_argument("--clean", action="store_true")
    parser.add_argument("--watch-pattern", default="lean", help="Substring to match worker comms/cmdlines")
    parser.add_argument("--extra-pid-name", default="lean-zygote", help="Also sample any processes matching this name")
    parser.add_argument("--json-out", default="")
    parser.add_argument("cmd", nargs=argparse.REMAINDER)
    args = parser.parse_args()

    cmd = args.cmd
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        print("Error: missing command after --", file=sys.stderr)
        sys.exit(2)

    workdir = Path(args.workdir)
    if args.clean:
        lake_build = workdir / ".lake" / "build"
        if lake_build.exists():
            subprocess.run(["rm", "-rf", str(lake_build)], check=True)

    t0 = time.monotonic()
    proc = subprocess.Popen(cmd, cwd=str(workdir), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

    peak_per_pid_rss_kb = {}
    peak_per_pid_priv_kb = {}
    peak_per_pid_pss_kb = {}
    peak_agg_rss_kb = 0
    peak_agg_pss_kb = 0
    peak_agg_priv_kb = 0
    peak_worker_count = 0
    samples = 0

    while proc.poll() is None:
        children, comms = read_proc_children()
        desc = collect_descendants(proc.pid, children)
        extra_pids = [
            p for p, c in comms.items()
            if args.extra_pid_name and (args.extra_pid_name in c or args.extra_pid_name in read_cmdline(p))
        ]
        all_pids = sorted(set(desc) | set(extra_pids))

        agg_rss = 0
        agg_pss = 0
        agg_priv = 0
        worker_count = 0

        for pid in all_pids:
            comm = comms.get(pid, "")
            cmdline = read_cmdline(pid)
            is_target = (
                pid == proc.pid
                or args.watch_pattern in comm
                or args.watch_pattern in cmdline
                or (args.extra_pid_name and (args.extra_pid_name in comm or args.extra_pid_name in cmdline))
            )
            if not is_target:
                continue
            sm = read_smaps_rollup(pid)
            if not sm:
                continue
            rss = sm.get("Rss", 0)
            pss = sm.get("Pss", 0)
            priv = sm.get("Private_Dirty", 0) + sm.get("Private_Clean", 0)
            agg_rss += rss
            agg_pss += pss
            agg_priv += priv
            if pid != proc.pid:
                worker_count += 1
                peak_per_pid_rss_kb[pid] = max(peak_per_pid_rss_kb.get(pid, 0), rss)
                peak_per_pid_pss_kb[pid] = max(peak_per_pid_pss_kb.get(pid, 0), pss)
                peak_per_pid_priv_kb[pid] = max(peak_per_pid_priv_kb.get(pid, 0), priv)

        peak_agg_rss_kb = max(peak_agg_rss_kb, agg_rss)
        peak_agg_pss_kb = max(peak_agg_pss_kb, agg_pss)
        peak_agg_priv_kb = max(peak_agg_priv_kb, agg_priv)
        peak_worker_count = max(peak_worker_count, worker_count)
        samples += 1
        time.sleep(0.05)

    stdout_data, _ = proc.communicate()
    elapsed = time.monotonic() - t0

    per_worker_rss = sorted(peak_per_pid_rss_kb.values())
    per_worker_pss = sorted(peak_per_pid_pss_kb.values())
    per_worker_priv = sorted(peak_per_pid_priv_kb.values())

    report = {
        "cmd": cmd,
        "exit_code": proc.returncode,
        "elapsed_sec": round(elapsed, 3),
        "samples": samples,
        "observed_workers": len(per_worker_rss),
        "peak_concurrent_workers": peak_worker_count,
        "peak_agg_rss_mb": round(peak_agg_rss_kb / 1024.0, 2),
        "peak_agg_pss_mb": round(peak_agg_pss_kb / 1024.0, 2),
        "peak_agg_private_mb": round(peak_agg_priv_kb / 1024.0, 2),
        "max_worker_rss_mb": round((per_worker_rss[-1] if per_worker_rss else 0) / 1024.0, 2),
        "median_worker_rss_mb": round((per_worker_rss[len(per_worker_rss) // 2] if per_worker_rss else 0) / 1024.0, 2),
        "max_worker_pss_mb": round((per_worker_pss[-1] if per_worker_pss else 0) / 1024.0, 2),
        "median_worker_pss_mb": round((per_worker_pss[len(per_worker_pss) // 2] if per_worker_pss else 0) / 1024.0, 2),
        "max_worker_private_mb": round((per_worker_priv[-1] if per_worker_priv else 0) / 1024.0, 2),
        "median_worker_private_mb": round((per_worker_priv[len(per_worker_priv) // 2] if per_worker_priv else 0) / 1024.0, 2),
    }

    print(stdout_data)
    print("BENCHMARK_SUMMARY:", json.dumps(report, indent=2))
    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2)
    sys.exit(proc.returncode)


if __name__ == "__main__":
    main()
