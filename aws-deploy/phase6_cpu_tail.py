"""Run the pinned Phase 6 CPU tail on a Linux c7a.24xlarge."""
import argparse
import fcntl
import hashlib
import json
import os
import resource
import shutil
import subprocess
import time
from pathlib import Path

THREADS = (96, 48, 16)
EXPECTED = {"Full_Mathlib": (775326, 0), "PrimeNumberTheoremAnd": (544714, 2)}

def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as file:
        for chunk in iter(lambda: file.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()

def write_json(path, data):
    tmp = path.with_suffix(".json.part")
    tmp.write_text(json.dumps(data, indent=2) + "\n")
    tmp.replace(path)

def run(command, log, env):
    print(f"Running {log.stem}", flush=True)
    with log.open("w") as file:
        start = time.monotonic()
        result = subprocess.run([str(a) for a in command], env=env, stdout=file, stderr=subprocess.STDOUT)
    return result.returncode, time.monotonic() - start

def valid(record, log, count, expected, threads):
    return (record.get("exit_code") == expected and
            record.get("verdict") == ("Accepted" if expected == 0 else "Declined") and
            record.get("total_decls") == count and record.get("threads") == threads and
            record.get("backend_mode") == "cpu" and record.get("prefix_skipped") == 0 and
            log.is_file() and (expected == 0 or
            "declined at 528744: use of the sorryAx axiom" in log.read_text(errors="replace")))

def benchmark(args):
    metadata = json.loads((args.inputs / "inputs.json").read_text())
    paths = [args.inputs / p for p in metadata["load_paths"]]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
    env.pop("LEAN_NUM_THREADS", None)
    for name, (historic_count, expected) in EXPECTED.items():
        count = args.reference_count if name == "Full_Mathlib" else historic_count
        item = metadata["packages"][name]
        root = args.inputs / item["file"]
        if (item["total_decls"], item["exit"]) != (historic_count, expected) or sha(root) != item["sha256"]:
            raise ValueError(f"Input identity mismatch for {name}")
        tag = "full_mathlib" if name == "Full_Mathlib" else name
        stock = args.out / f"{tag}_stock_leanchecker.json"
        stock_log = stock.with_suffix(".log")
        if not (stock.is_file() and json.loads(stock.read_text()).get("exit_code") == 0 and stock_log.is_file()):
            cmd = [str(args.leanchecker), "--fresh", item["module"]]
            log = stock.with_suffix(".log.part")
            code, elapsed = run(cmd, log, env)
            if code:
                raise RuntimeError(f"Stock checker exit {code}, see {log}")
            log.replace(stock_log)
            write_json(stock, {"cmd": cmd, "LEAN_PATH": env["LEAN_PATH"], "exit_code": code,
                               "elapsed_sec": elapsed, "root_olean_sha256": item["sha256"]})
        snapshot = args.scratch / f"{tag}_scale.cgsnap"
        for mode in (["cold", "snap"] if expected == 0 else ["cold"]):
            for threads in THREADS:
                dest = args.out / f"{tag}_congpu_{mode}_{threads}t.json"
                log = dest.with_suffix(".log")
                save_snapshot = mode == "cold" and threads == 96 and expected == 0
                if dest.is_file() and valid(json.loads(dest.read_text()), log, count, expected, threads):
                    if not save_snapshot or snapshot.is_file():
                        continue
                partial = dest.with_suffix(".json.part")
                partial_log = dest.with_suffix(".log.part")
                cmd = [args.con_gpu, "verify", root, "--fresh", "--backend", "cpu",
                       "--jobs", threads, "--trust-bv-decide-axioms",
                       "--load-paths", ",".join(map(str, paths)), "--json-out", partial]
                if save_snapshot:
                    cmd.extend(["--save-snapshot", snapshot.with_suffix(".part.cgsnap")])
                elif mode == "snap":
                    cmd.extend(["--snapshot", snapshot])
                # An earlier count comparison can fail after the verifier writes its
                # complete JSON, log and Accepted snapshot. Retain then reuse that run.
                raw = args.out / "initial_count_check"
                replay = False
                if partial.is_file():
                    raw.mkdir(exist_ok=True)
                    for original in (partial, partial_log):
                        if original.is_file():
                            saved = raw / original.name
                            if not saved.exists():
                                shutil.copyfile(original, saved)
                            elif sha(saved) != sha(original):
                                raise RuntimeError(f"Conflicting initial evidence {saved}")
                    try:
                        previous = json.loads(partial.read_text())
                    except (ValueError, UnicodeError):
                        previous = {}
                    replay = (valid(previous, partial_log, count, expected, threads) and
                              (not save_snapshot or snapshot.with_suffix(".part.cgsnap").is_file()))
                if replay:
                    print(f"Recovering complete initial run {dest.stem}", flush=True)
                    code = expected
                else:
                    partial.unlink(missing_ok=True)
                    code, _ = run(cmd, partial_log, env)
                if code != expected or not partial.is_file() or not valid(
                        json.loads(partial.read_text()), partial_log, count, expected, threads):
                    raise RuntimeError(f"CPU identity/verdict failure. See {partial_log}")
                if save_snapshot:
                    snapshot.with_suffix(".part.cgsnap").replace(snapshot)
                partial_log.replace(log)
                partial.replace(dest)
    files = sorted(list(args.out.glob("*.json")) + list(args.out.glob("*.log")))
    manifest = args.out / "tail_sha256sums.txt.part"
    manifest.write_text("".join(f"{sha(p)}  {p.name}\n" for p in files if p.name != "console.log"))
    manifest.replace(args.out / "tail_sha256sums.txt")
    print("Phase 6 CPU tail complete", flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("inputs", "out", "scratch", "con-gpu", "leanchecker"):
        parser.add_argument(f"--{arg}", type=lambda p: Path(p).resolve(), required=True)
    parser.add_argument("--full-mathlib-reference", required=True, type=lambda p: Path(p).resolve(),
                        help="Measured cold CPU or hybrid JSON for this shared Full Mathlib cohort")
    args = parser.parse_args()
    reference = json.loads(args.full_mathlib_reference.read_text(encoding="utf-8-sig"))
    if (reference.get("verdict") != "Accepted" or reference.get("exit_code") != 0 or
            reference.get("prefix_skipped") != 0 or reference.get("backend_mode") not in ("cpu","hybrid")
            or not isinstance(reference.get("total_decls"), int) or reference["total_decls"] <= 0):
        raise ValueError("Invalid shared Full Mathlib reference")
    args.reference_count = reference["total_decls"]
    if len(os.sched_getaffinity(0)) != 96:
        raise RuntimeError("The c7a.24xlarge series requires exactly 96 visible vCPUs")
    _, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    resource.setrlimit(resource.RLIMIT_NOFILE, (65536, hard))
    args.out.mkdir(parents=True, exist_ok=True)
    args.scratch.mkdir(parents=True, exist_ok=True)
    with (args.out / ".tail.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        provenance = {"runner_sha256": sha(Path(__file__)), "con_gpu_sha256": sha(args.con_gpu),
                      "leanchecker_entry_sha256": sha(args.leanchecker),
                      "inputs_sha256": sha(args.inputs / "inputs.json"),
                      "input_hash_manifest_sha256": sha(args.inputs / "SHA256SUMS"),
                      "visible_cpus": len(os.sched_getaffinity(0))}
        actual_stock = args.leanchecker.parent / "stock" / "bin" / "leanchecker"
        if actual_stock.exists():
            provenance["stock_binary_sha256"] = sha(actual_stock)
        identity = args.out / "tail_provenance.json"
        provenance["full_mathlib_cohort"] = {
            "historical_rx_decl_count": EXPECTED["Full_Mathlib"][0],
            "reference_sha256": sha(args.full_mathlib_reference),
            "reference_decl_count": args.reference_count,
            "reference_backend": reference["backend_mode"],
            "reference_device": reference.get("device_name")}
        if identity.exists():
            prior = json.loads(identity.read_text())
            if prior != provenance:
                v1 = {k:v for k,v in provenance.items() if k != "full_mathlib_cohort"}
                v1["runner_sha256"] = "819969e5b4b2d003841a1589bf3a16bf8bb388fa001b89680bd78729d0d6152b"
                if prior != v1:
                    raise RuntimeError("Prior CPU receipt belongs to different inputs or executables")
                raw = args.out / "initial_count_check"
                raw.mkdir(exist_ok=True)
                old = raw / "tail_provenance.json"
                if old.exists() and sha(old) != sha(identity):
                    raise RuntimeError("Conflicting initial provenance")
                if not old.exists():
                    shutil.copyfile(identity, old)
        reference_copy = args.out / "full_mathlib_reference.json"
        if reference_copy.exists() and sha(reference_copy) != sha(args.full_mathlib_reference):
            raise RuntimeError("Conflicting saved Full Mathlib reference")
        if not reference_copy.exists():
            shutil.copyfile(args.full_mathlib_reference, reference_copy)
        subprocess.run(["sha256sum", "-c", "--quiet", "SHA256SUMS"], cwd=args.inputs, check=True)
        write_json(identity, provenance)
        benchmark(args)

if __name__ == "__main__":
    main()
