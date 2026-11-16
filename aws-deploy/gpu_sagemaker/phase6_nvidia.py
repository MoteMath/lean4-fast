"""Verify Phase 6 NVIDIA Vulkan results against the RX Full Mathlib and corrected PNT runs."""
import argparse
import hashlib
import json
import re
import sys
import tarfile
from pathlib import Path


def check(condition, message):
    if not condition:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def checksum(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def checked_manifest(directory):
    names = set()
    for line in (directory / "sha256sums.txt").read_text().splitlines():
        match = re.fullmatch(r"([0-9a-fA-F]{64}) [ *](?:\./)?([^/\\]+)", line)
        check(match is not None, f"{directory}: malformed SHA256 record: {line!r}")
        digest, name = match.groups()
        check(name not in names, f"{directory}: duplicate SHA256 for {name}")
        check(checksum(directory / name) == digest.lower(), f"{directory / name}: SHA256 mismatch")
        names.add(name)
    check(names, f"{directory}: empty SHA256 manifest")
    return names


def gpu_result(data, model):
    check(data.get("device_name") == f"NVIDIA {model}", f"expected NVIDIA {model}, got {data.get('device_name')}")
    check(data.get("device_type") == "DiscreteGpu" and data.get("device_backend") == "Vulkan",
          "expected a discrete Vulkan adapter")
    if data.get("backend_mode") == "both":
        check(data.get("all_passed") is True, "synthetic benchmark failed")
    else:
        check(data.get("backend_mode") == "hybrid" and data.get("gpu_verified_count", 0) > 0
              and data.get("gpu_kernel_ns", 0) > 0, "missing hybrid GPU execution")


def decline(path):
    text = path.read_text(encoding="utf-8-sig")
    records = re.findall(r"^\s*declined at (\d+): ([^\r\n]+)$", text, flags=re.MULTILINE)
    check(len(records) == 1, f"{path}: expected exactly one decline location")
    return records[0]


TAIL = ("Full_Mathlib", "PrimeNumberTheoremAnd")
PACKAGES = ("SyntheticBench", "DownstreamBench", "Init_Std", "Batteries", "Aesop", "DocGen4",
            "ImportGraph", "Qq", "Plausible", "Cedar", "Mathlib_Real_Basic", *TAIL)


def find_result_dir(result_dirs, filename):
    matches = [directory for directory, names in result_dirs.items() if filename in names]
    check(len(matches) == 1, f"expected a single manifest covering {filename}, found {matches}")
    return matches[0]


def supplement_members(path):
    members = {}
    with tarfile.open(path, "r|zst") as stream:
        for member in stream:
            if member.isdir():
                continue
            check(member.isfile(), f"{path}: unexpected non-file {member.name}")
            name = member.name.removeprefix("./")
            check(name not in members, f"{path}: duplicate {name}")
            members[name] = hashlib.file_digest(stream.extractfile(member), "sha256").hexdigest()
    return members


def compare_supplements(old, new):
    # Prove that unchanged jobs saw exactly the same files and manifest. The
    # container's only additional input is the separately pinned base archive.
    left, right = supplement_members(old), supplement_members(new)
    check(set(left) == set(right), "supplement member set differs")
    changed = sorted(k for k in left if left[k] != right[k])
    check(changed == ["ImportGraph/manifest.env"], f"unexpected supplement differences: {changed}")
    packages = sorted(pkg for pkg in PACKAGES if pkg != "ImportGraph" and f"{pkg}/manifest.env" in left)
    check(len(packages) == 10, "expected 10 unchanged package manifests")
    return {"old_sha256": checksum(old), "new_sha256": checksum(new), "member_count": len(left),
            "unchanged_members": len(left)-1, "changed_member": changed[0],
            "old_member_sha256": left[changed[0]], "new_member_sha256": right[changed[0]],
            "equivalent_packages": packages}


def compare(phase_dir, archive_hashes, binary_sha, packages, models=("L40S", "A10G"), equivalence=None):
    check(re.fullmatch(r"[0-9a-fA-F]{64}", binary_sha), "invalid verifier SHA256")
    for package in packages:
        check(re.fullmatch(r"[0-9a-fA-F]{64}", archive_hashes.get(package, "")), f"{package}: missing input hash")
    rx = phase_dir / "local_rx7900xtx"
    rx_supplement = phase_dir / "local_rx7900xtx_supplement"
    fixed_rx = phase_dir / "pnt_540915_replay"
    rx_sources = {rx: checked_manifest(rx)}
    if (rx_supplement / "sha256sums.txt").is_file():
        rx_sources[rx_supplement] = checked_manifest(rx_supplement)
    results = []
    for model, folder in [("L40S", "gpu_l40s_g6e"), ("A10G", "gpu_a10g_g5")]:
        if model not in models:
            continue
        root = phase_dir / folder
        manifests = sorted(root.glob("sha256sums.txt")) + sorted(root.glob("*/sha256sums.txt"))
        check(manifests, f"{root}: no NVIDIA output checksum manifests")
        indexes = {mf.parent: checked_manifest(mf.parent) for mf in manifests}
        for directory, names in indexes.items():
            def artifact(name):
                check(name in names, f"{directory}: {name} missing from verified manifest")
                return directory / name

            check(artifact("con_gpu_binary.sha256").read_text().strip() == binary_sha.lower(),
                  f"{model}: unrecognized verifier binary")
            gpu_result(load(artifact("bench_synthetic.json")), model)
            soundness = artifact("test_soundness.log").read_text()
            check(f"on NVIDIA {model} (backend=Vulkan)" in soundness and
                  "[PASS] Pipeline A con-leche differential soundness:" in soundness and "[FAIL]" not in soundness,
                  f"{model}: missing successful NVIDIA soundness suite")
        for package in packages:
            name = f"{package}_archive.sha256"
            expected_sha = archive_hashes[package].lower()
            allowed_shas = [expected_sha]
            if (equivalence and package in equivalence["equivalent_packages"]
                    and expected_sha == equivalence["new_sha256"]):
                allowed_shas.append(equivalence["old_sha256"])
            candidates = [(directory, (directory / name).read_text().split()[0]) for directory, names in indexes.items()
                          if name in names]
            check(candidates, f"expected a single manifest covering {name}, found none")
            directory = None
            for sha in allowed_shas:
                matching = [d for d, observed in candidates if observed == sha]
                check(len(matching) <= 1, f"{name}: duplicate output for {sha}: {matching}")
                if matching:
                    directory = matching[0]
                    break
            check(directory is not None, f"{model}/{package}: input archive SHA256 mismatch")

            def read_artifact(name):
                check(name in indexes[directory], f"{directory}: missing verified {name}")
                return directory / name

            archive_record = read_artifact(f"{package}_archive.sha256").read_text().split()
            check(len(archive_record) == 2 and archive_record[0] in allowed_shas,
                  f"{model}/{package}: input archive SHA256 mismatch")
            if archive_record[1] == "phase6_11_supplement.tar.zst":
                base_hash = read_artifact(f"{package}_base_archive.sha256").read_text().split()[0]
                check(base_hash == archive_hashes["Full_Mathlib"].lower(), f"{model}/{package}: shared base differs")
            pnt = package == "PrimeNumberTheoremAnd"
            declined = package in ("Cedar", "PrimeNumberTheoremAnd")
            modes = ["hybrid_cold", "cpu_cold"]
            if not declined:
                modes += ["hybrid_snap", "cpu_snap"]
                if package in ("Full_Mathlib", "Mathlib_Real_Basic"):
                    modes.append("hybrid_hashcheck")
            for mode in modes:
                name = f"{package}_{mode}.json"
                rx_mode = "hybrid_snap" if mode == "hybrid_hashcheck" else mode
                rx_name = f"{package}_{rx_mode}.json"
                if name in rx_sources.get(rx_supplement, set()):
                    rx_name = name
                if pnt and mode == "hybrid_cold":
                    baseline = fixed_rx / "rx_full.json"
                elif rx_name in rx_sources.get(rx_supplement, set()):
                    baseline = rx_supplement / rx_name
                else:
                    check(package in TAIL, f"{package}: missing shared-corpus RX reference {rx_name}")
                    check(rx_name in rx_sources[rx], f"{package}: missing verified RX baseline {rx_name}")
                    baseline = rx / rx_name
                reference = load(baseline)
                data = load(read_artifact(name))
                for field in ("total_decls", "prefix_skipped", "exit_code", "verdict", "backend_mode", "gpu_rejected_count"):
                    check(data[field] == reference[field],
                          f"{model}/{name}: {field}={data[field]} vs RX {reference[field]}")
                check(data["gpu_rejected_count"] == 0 and
                      (data["verdict"], data["exit_code"]) == (("Declined", 2) if declined else ("Accepted", 0)),
                      f"{model}/{name}: unexpected verdict or GPU rejection")
                if mode.startswith("hybrid"):
                    gpu_result(data, model)
                    check(data["eligible_jobs_count"] == reference["eligible_jobs_count"],
                          f"{name}: eligible count differs from RX")
                    check(data["gpu_verified_count"] + data["gpu_rejected_count"] + data["delegated_count"] ==
                          data["total_decls"] - data["prefix_skipped"], f"{name}: declaration accounting mismatch")
                    if not declined:
                        check(data["host_verified_delegated"] == data["delegated_count"],
                              f"{name}: host fallback count mismatch")
                else:
                    check(data["device_type"] == "Cpu" and data["device_backend"] == "Rayon", f"{name}: expected CPU")
                if declined:
                    if pnt:
                        expected = decline(fixed_rx / "rx_full.log")
                        check(expected == ("528744", "use of the sorryAx axiom"), "unexpected corrected RX PNT decline")
                    else:
                        rx_log = f"{package}_hybrid_cold.log"
                        rx_directory = find_result_dir(rx_sources, rx_log)
                        expected = decline(rx_directory / rx_log)
                    check(decline(read_artifact(f"{package}_{mode}.log")) == expected, f"{name}: decline differs from RX")
                results.append({"package": package, "mode": mode, "model": model,
                                "rx_reference": str(baseline.relative_to(phase_dir)), "measured_archive_sha256": archive_record[0],
                                "verdict": data["verdict"], "total_decls": data["total_decls"],
                                "gpu_rejected_count": data["gpu_rejected_count"], "wall_ns": data["wall_ns"]})
    report = {"input_archive_sha256": archive_hashes, "verifier_sha256": binary_sha, "verified_results": results}
    if equivalence is not None:
        report["supplement_equivalence"] = equivalence
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    device = commands.add_parser("check-device")
    device.add_argument("model", choices=["L40S", "A10G"])
    device.add_argument("json", type=Path)
    parity = commands.add_parser("compare")
    parity.add_argument("phase_dir", type=Path)
    parity.add_argument("--model", choices=["L40S", "A10G"], help="audit one completed hardware run")
    parity.add_argument("--scope", choices=["all", "tails"], default="all")
    parity.add_argument("--verifier-sha256", required=True)
    parity.add_argument("--equivalent-supplements", type=Path, nargs=2, metavar=("OLD", "NEW"),
                        help="independently verify that only ImportGraph changed (Python 3.14+)")
    inputs = parity.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--archive-sha256", help="digest if all selected roots are in one archive")
    inputs.add_argument("--archive-map", type=Path, help="JSON mapping package names to staged archive SHA256")
    args = parser.parse_args()
    if args.command == "check-device":
        gpu_result(load(args.json), args.model)
    else:
        packages = TAIL if args.scope == "tails" else PACKAGES
        hashes = load(args.archive_map) if args.archive_map else dict.fromkeys(packages, args.archive_sha256)
        models = [args.model] if args.model else ["L40S", "A10G"]
        equivalence = compare_supplements(*args.equivalent_supplements) if args.equivalent_supplements else None
        print(json.dumps(compare(args.phase_dir, hashes, args.verifier_sha256, packages, models, equivalence), indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        sys.exit(str(error))
