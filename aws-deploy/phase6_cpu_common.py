"""Replay the eleven supplemental common roots at 96T on the shared input bundle."""
import argparse
import hashlib
import json
import os
import resource
import shlex
import subprocess
from pathlib import Path

PACKAGES = ("Aesop", "Batteries", "Qq", "Plausible", "ImportGraph", "DocGen4", "Cedar",
            "Init_Std", "SyntheticBench", "DownstreamBench", "Mathlib_Real_Basic")

def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as src:
        for block in iter(lambda: src.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()

def decode_manifest(file, inputs):
    fields = {}
    for line in file.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, raw = line.split("=", 1)
        fields[key] = shlex.split(raw)[0]
    def resolve(names):
        paths = [(file.parent / name).resolve() for name in names]
        if not all(inputs in path.parents and path.exists() for path in paths):
            raise ValueError(f"Missing or external input path from {file}")
        return paths
    return (resolve(fields["ROOT_OLEANS"].split()), resolve(fields["LOAD_PATHS"].split(":")),
            int(fields["EXPECTED_EXIT"]))

def run(args):
    _, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    resource.setrlimit(resource.RLIMIT_NOFILE, (65536, hard))
    if len(os.sched_getaffinity(0)) != 96:
        raise ValueError("Expected 96 visible c7a vCPUs")
    out = args.out / "shared_cpu_96t"
    out.mkdir(parents=True, exist_ok=True)
    provenance = {"con_gpu_sha256": sha(args.con_gpu), "runner_sha256": sha(Path(__file__)),
                  "shared_sha256manifest": sha(args.inputs / "SHA256SUMS"), "inputs": {}}
    for package in PACKAGES:
        manifest = args.inputs / package / "manifest.env"
        roots, paths, code = decode_manifest(manifest, args.inputs)
        if code != (2 if package == "Cedar" else 0):
            raise ValueError(f"Unexpected manifest exit for {package}")
        provenance["inputs"][package] = {"manifest_sha256": sha(manifest),
            "roots_sha256": {str(p.relative_to(args.inputs)): sha(p) for p in roots}}
        json_out = out / f"{package}_cpu_cold.json"
        log = out / f"{package}_cpu_cold.log"
        part = json_out.with_suffix(".json.part")
        log_part = log.with_suffix(".log.part")
        part.unlink(missing_ok=True)
        argv = [str(args.con_gpu), "verify", *map(str, roots), "--fresh", "--backend", "cpu",
                "--jobs", "96", "--trust-bv-decide-axioms", "--load-paths", ",".join(map(str, paths)),
                "--json-out", str(part)]
        print(f"Shared input CPU replay {package}", flush=True)
        with log_part.open("w") as f:
            rc = subprocess.run(argv, stdout=f, stderr=subprocess.STDOUT).returncode
        if rc != code:
            raise RuntimeError(f"Unexpected verifier exit {rc} for {package}, see {log_part}")
        row = json.loads(part.read_text())
        if (row["exit_code"] != code or row["verdict"] != ("Declined" if code else "Accepted")
                or row["threads"] != 96 or row["prefix_skipped"] != 0 or row["backend_mode"] != "cpu"
                or row["total_decls"] <= 0):
            raise RuntimeError(f"Invalid verifier metadata for {package}")
        log_part.replace(log)
        part.replace(json_out)
    (out / "shared_cpu_provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    files = sorted([*out.glob("*.json"), *out.glob("*.log")])
    (out / "sha256sums.txt").write_text("".join(f"{sha(p)}  {p.name}\n" for p in files))
    print("Supplemental common CPU replay complete", flush=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for field in ("inputs", "out", "con-gpu"):
        parser.add_argument("--" + field, type=lambda p: Path(p).resolve(), required=True)
    run(parser.parse_args())
