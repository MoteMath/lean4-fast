"""Index Phase 6 measurements and render the two reports from audited receipts."""
import argparse
import csv
import hashlib
import json
import re
from collections import Counter
from pathlib import Path, PureWindowsPath

HERE = Path(__file__).resolve().parent
TAIL = ("Full_Mathlib", "PrimeNumberTheoremAnd")
PACKAGES = ("SyntheticBench", "DownstreamBench", "Init_Std", "Batteries", "Aesop", "DocGen4",
            "ImportGraph", "Qq", "Plausible", "Cedar", "Mathlib_Real_Basic", *TAIL, "DownstreamReal")
ALIASES = {re.sub("[^a-z0-9]", "", package.lower()): package for package in PACKAGES}
ALIASES.update(synthetic="SyntheticBench", realbasic="Mathlib_Real_Basic")
CPU = "c7a.24xlarge"
RX = "RX 7900 XTX"
NVIDIA = {"gpu_l40s_g6e": "L40S", "gpu_a10g_g5": "A10G"}
FIELDS = ("record_type", "package", "platform", "run", "mode", "threads", "exit_code", "verdict",
          "elapsed_sec", "total_decls", "gpu_verified_count", "gpu_rejected_count", "delegated_count",
          "load_ns", "total_verify_ns", "gpu_kernel_ns", "wall_ns", "workload", "ops", "clauses", "gpu_total_ns",
          "cpu_rayon_ns", "source", "source_sha256")


def read(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def canonical(name):
    normalized = re.sub("[^a-z0-9]", "", name.lower())
    return ALIASES.get(normalized, name)


def check_manifests(root):
    summaries = []
    files = set()
    for name in ("sha256sums.txt", "tail_sha256sums.txt"):
        for path in sorted(root.rglob(name)):
            entries = set()
            for line in path.read_text(encoding="utf-8-sig").splitlines():
                if not line.strip():
                    continue
                m = re.fullmatch(r"([0-9a-fA-F]{64})\s+[*]?(.+)", line)
                require(m, f"invalid checksum line in {path}")
                candidate = (path.parent / m[2]).resolve()
                require(candidate.is_relative_to(path.parent.resolve()), f"out-of-tree checksum in {path}")
                require(candidate not in entries, f"duplicate {candidate} in {path}")
                require(digest(candidate) == m[1].lower(), f"checksum mismatch for {candidate}")
                entries.add(candidate)
            require(entries, f"empty manifest {path}")
            files.update(entries)
            summaries.append({"source": path.relative_to(root).as_posix(), "sha256": digest(path),
                              "entries_checked": len(entries)})
    return summaries, files


def origin(path, root):
    parts = path.relative_to(root).parts
    if "initial_count_check" in parts or path.name == "full_mathlib_reference.json":
        return None
    area = parts[0]
    if (path.parent / "shared_cpu_provenance.json").exists():
        return CPU, "shared CPU replay"
    if (path.parent / "tail_provenance.json").exists():
        return CPU, "CPU tail replay"
    if area == "cpu_c7a_96vcpu":
        return CPU, "archived CPU run"
    if area == "local_windows_cpu":
        return "Windows CPU", "supplemental local CPU run"
    if area == "local_rx7900xtx":
        return RX, "archived RX run"
    if area == "pnt_540915_replay" and path.name == "rx_full.json":
        return RX, "corrected full PNT replay"
    if area == "local_rx7900xtx_supplement":
        return RX, "supplemental RX run"
    if area in NVIDIA:
        return NVIDIA[area], "SageMaker run"
    return None


def mode_and_package(stem, data):
    if stem == "rx_full":
        return "con_gpu_verify", TAIL[1], "hybrid_cold"
    if "total_decls" in data and "backend_mode" in data:
        parts = re.fullmatch(r"(.+?)_congpu_(cold|snap)_(\d+)t", stem, re.I)
        if parts:
            return "con_gpu_verify", canonical(parts[1]), "cpu_" + parts[2].lower()
        parts = re.fullmatch(r"(.+?)_((?:hybrid|cpu)_(?:cold|snap|hashcheck))", stem, re.I)
        if parts:
            return "con_gpu_verify", canonical(parts[1]), parts[2].lower()
        raise ValueError(f"unrecognized verifier mode in {stem}")
    if "bignum_nat" in data or "lrat" in data:
        return "synthetic", "bench-synthetic", data["backend_mode"]
    suffix = re.fullmatch(r"(.+?)_stock_leanchecker", stem, re.I)
    if suffix and "exit_code" in data:
        return "stock_leanchecker", canonical(suffix[1]), "stock_fresh"
    if "cmd" in data and "elapsed_sec" in data:
        parts = re.fullmatch(r"(.+?)_(stock|p6_cold|p6_zygote)(.*)", stem, re.I)
        if parts:
            return "lake_build", canonical(parts[1]), parts[2] + parts[3]
    return None


def collect(root, indexed_files):
    rows = []
    # The archived measurements use case-insensitive Windows path ordering.
    for path in sorted(root.rglob("*.json"), key=PureWindowsPath):
        identity = origin(path, root)
        if not identity:
            continue
        data = read(path)
        if not isinstance(data, dict):
            continue
        tags = mode_and_package(path.stem, data)
        if not tags:
            continue
        kind, package, mode = tags
        platform, run = identity
        if run in ("CPU tail replay", "shared CPU replay", "SageMaker run"):
            require(path.resolve() in indexed_files, f"unmanifested measurement {path}")
        row = {key: data[key] for key in FIELDS if key in data}
        if "wall_ns" in data:
            row["elapsed_sec"] = data["wall_ns"] / 1_000_000_000
        row.update(record_type=kind, package=package, platform=platform, run=run, mode=mode,
                   source=path.relative_to(root).as_posix(), source_sha256=digest(path), metrics=data)
        if kind == "synthetic":
            for workload in ("bignum_nat", "lrat"):
                for sample in data[workload]:
                    item = {**row, **sample, "workload": workload, "verdict": "Pass" if data["all_passed"] else "Fail"}
                    item["metrics"] = {key: value for key, value in data.items() if key not in ("bignum_nat", "lrat")}
                    item["metrics"]["sample"] = sample
                    rows.append(item)
        else:
            rows.append(row)
    return rows


def build_comparisons(root):
    comparisons = {}
    for path in sorted((root / "cpu_c7a_96vcpu").glob("*_sha256_compare.txt")):
        modes = {}
        for line in path.read_text().splitlines():
            match = re.fullmatch(r"(\S+) (\S+) \(non-BV\): (count_a=\d+ count_b=\d+ common_non_bv=\d+ matched=\d+ mismatched=\d+)", line)
            if match:
                stats = {key: int(value) for key, value in re.findall(r"(\w+)=(\d+)", match[3])}
                require(stats["common_non_bv"] == stats["matched"] + stats["mismatched"], f"invalid comparison in {path}")
                modes[match[2]] = stats
        require(modes, f"no comparison records in {path}")
        name = canonical(path.name.removesuffix("_sha256_compare.txt"))
        comparisons[name] = {"source": path.relative_to(root).as_posix(), "sha256": digest(path), "modes": modes}
    return comparisons


def validate_cpu(rows, root, archive):
    candidates = [p for p in root.rglob("tail_provenance.json") if (p.parent / "tail_sha256sums.txt").exists()]
    require(len(candidates) == 1, "a single completed c7a tail with a checksum manifest is required")
    provenance = read(candidates[0])
    require(provenance["input_hash_manifest_sha256"] == archive["sha256sums_digest"], "CPU input digest mismatch")
    require(provenance["visible_cpus"] == 96, "c7a CPU count mismatch")
    for package in TAIL:
        expected = archive["packages"][package]
        table = [r for r in rows if r["run"] == "CPU tail replay" and r["package"] == package]
        stock = [r for r in table if r["record_type"] == "stock_leanchecker"]
        require(len(stock) == 1 and stock[0]["exit_code"] == 0, f"missing stock success for {package}")
        require(stock[0]["metrics"]["root_olean_sha256"] == expected["sha256"], f"stock root mismatch for {package}")
        verifier = [r for r in table if r["record_type"] == "con_gpu_verify"]
        modes = ("cpu_cold", "cpu_snap") if package == TAIL[0] else ("cpu_cold",)
        need = {(m,t) for m in modes for t in (16,48,96)}
        require(len(verifier) == len(need) and {(r["mode"],r["threads"]) for r in verifier} == need,
                f"incomplete CPU modes for {package}")
        counts = {r["total_decls"] for r in verifier}
        require(len(counts) == 1, f"inconsistent c7a declaration counts across {package} runs")
        if package == TAIL[1]:
            require(counts == {544714}, "PNT input differs from corrected RX replay")
        for r in verifier:
            require(r["exit_code"] == expected["exit"] and r["total_decls"] > 0
                    and r["verdict"] == ("Accepted" if expected["exit"] == 0 else "Declined"), r["source"])
            if expected["exit"] == 2:
                log = (root / r["source"]).with_suffix(".log").read_text(encoding="utf-8-sig")
                require("declined at 528744: use of the sorryAx axiom" in log, f"unexpected PNT decline for {r['source']}")
    reference = candidates[0].parent / "full_mathlib_reference.json"
    if reference.exists():
        full = read(reference)
        observed = get_row(rows, TAIL[0], CPU, "cpu_cold", 96)
        for key in ("total_decls", "verdict", "exit_code"):
            require(full[key] == observed[key], f"independent Full Mathlib reference differs on {key}")
        return {**provenance, "full_mathlib_reference": {"source": reference.relative_to(root).as_posix(),
                "sha256": digest(reference), "total_decls": full["total_decls"]}}
    return provenance


def get_row(rows, package, platform, mode, threads=None):
    found = [r for r in rows if r["package"] == package and r["platform"] == platform and r["mode"] == mode
             and (threads is None or threads == r.get("threads"))]
    if platform == CPU:
        found = [r for r in found if r["run"] == "CPU tail replay"]
    if platform == RX:
        if package == TAIL[1] and mode == "hybrid_cold":
            found = [r for r in found if r["run"] == "corrected full PNT replay"]
        else:
            supplemental = [r for r in found if r["run"] == "supplemental RX run"]
            found = supplemental or found
    require(len(found) == 1, f"expected one measurement for {package}/{platform}/{mode}/{threads}, got {len(found)}")
    return found[0]


def validate_nvidia_rows(root, rows, audited, models):
    packages = set(PACKAGES) - {"DownstreamReal"}
    required = set()
    for model in models:
        for package in packages:
            modes = {"hybrid_cold", "cpu_cold"}
            if package not in {"Cedar", "PrimeNumberTheoremAnd"}:
                modes.update({"hybrid_snap", "cpu_snap"})
            if package in {"Full_Mathlib", "Mathlib_Real_Basic"}:
                modes.add("hybrid_hashcheck")
            required.update((model, package, mode) for mode in modes)
    found = set()
    for result in audited:
        key = (result["model"], result["package"], result["mode"])
        require(key not in found and key in required, f"unexpected or duplicate audited mode {key}")
        found.add(key)
        model, package, mode = key
        measurement = get_row(rows, package, model, mode)
        reference = read(root / result["rx_reference"].replace(chr(92), "/"))
        for field in ("verdict", "total_decls", "gpu_rejected_count"):
            require(result[field] == measurement[field] == reference[field], f"{key}: mismatch on {field}")
        require(result["wall_ns"] == measurement["wall_ns"], f"{key}: timing differs from exported result")
    require(found == required, f"incomplete NVIDIA comparison; missing {sorted(required - found)}")


def report_sections(rows, cp, parity, manifests, archive, parity_name, cpu_audit, comparisons, corpus):
    audited = parity["verified_results"]
    counts = Counter(r["model"] for r in audited)
    interim = not counts["A10G"]
    status = "**Interim results. The A10G benchmark and its comparison are pending.**" if interim else ""
    def seconds(*args):
        return f'{get_row(rows,*args)["elapsed_sec"]:.3f}'
    table = ["| Package | Stock fresh | c7a CPU cold | c7a CPU snapshot | L40S hybrid cold | A10G hybrid cold | RX hybrid cold |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for p in TAIL:
        durations = [seconds(p,CPU,"stock_fresh"), seconds(p,CPU,"cpu_cold",96),
                     seconds(p,CPU,"cpu_snap",96) if p == TAIL[0] else "No snapshot",
                     seconds(p,"L40S","hybrid_cold"), "Pending" if interim else seconds(p,"A10G","hybrid_cold"), seconds(p,RX,"hybrid_cold")]
        table.append("| " + " | ".join([f"\x60{p}\x60", *durations]) + " |")
    package_count = len({r["package"] for r in audited})
    pnt = get_row(rows, TAIL[1], RX, "hybrid_cold")
    cpu_suffix = "The c7a stock checker exited 0 for both roots. The con-gpu rows use the corrected verifier, which accepted Full Mathlib and declined PrimeNumberTheoremAnd at declaration 528744 for use of the sorryAx axiom."
    measured = " and ".join(f"{counts[model]} {model}" for model in ("L40S", "A10G") if counts[model])
    coverage = (f"Compared {measured} measurements across "
                f"{package_count} packages with their RX references. The GPU identity, verdict, exit code, "
                "declaration count and GPU rejection checks passed for the modes in the comparison receipt.")
    prefix = "aws_ecosystem_phase6/"
    links = (f"[Measured rows (CSV)]({prefix}phase6_metrics_master.csv) | "
             f"[Metrics and receipt hashes (JSON)]({prefix}phase6_metrics_master.json) | "
             f"[NVIDIA comparison]({prefix}{parity_name})")
    common = ""
    cpu_status = ""
    if cpu_audit and cpu_audit.get("cpu_summary", {}).get("complete"):
        summary = cpu_audit["cpu_summary"]
        cpu_status = (f"The c7a CPU audit covers {summary['stock_records']} stock checks, "
                      f"{summary['scaling_records']} thread-scaling measurements and {summary['shared_cold_96t']} "
                      f"cold checks on the shared inputs. [CPU audit]({prefix}phase6_cpu_parity_audit.json)")
    if cpu_audit and cpu_audit["complete"]:
        common = (f"The c7a 96-thread cold replay agreed with RX hybrid and with CPU and hybrid mode on "
                  f"both NVIDIA hosts for all {len(cpu_audit['common_cold_parity'])} shared-input packages. "
                  f"[CPU scaling and four-platform comparison]({prefix}phase6_cpu_parity_audit.json)")
    full = get_row(rows, TAIL[0], RX, "hybrid_cold")
    archived = [row for row in rows if row["run"] == "archived RX run" and row["package"] == TAIL[0]
                and row["mode"] == "hybrid_cold"]
    note = f"Full Mathlib uses the {full['run']} with {full['total_decls']:,} declarations."
    if archived and archived[0]["total_decls"] != full["total_decls"]:
        note += f" The archived RX run had {archived[0]['total_decls']:,} declarations and is indexed separately."
    if corpus:
        require(corpus["current_L40S_stream_total_decls"] == full["total_decls"], "shared corpus count differs from RX")
        require(corpus["mathlib_root_sha256_both"] == archive["packages"]["Full_Mathlib"]["sha256"], "shared corpus root mismatch")
        note += (f" The root .olean hash matches across those inputs. {corpus['different_parts']:,} constituent files differ, "
                 f"and {corpus['distinct_name_set_difference_modules']} modules account for a net difference of "
                 f"{corpus['old_minus_new']} declarations. [Corpus comparison]({prefix}full_mathlib_corpus_comparison.json)")
    bench = "\n".join(["## 7. Phase 6 CPU and GPU replay", "", status, "",
        "Wall times are in seconds. The CPU cold and snapshot columns use 96 threads. "
        "The master table also includes the measured 16- and 48-thread runs. "
        "The RX column uses the corrected full PrimeNumberTheoremAnd replay. " + note, "",
        *table, "", cpu_suffix, cpu_status, "", coverage, common, "", links])
    build_lines = []
    for package in (TAIL[0], "Cedar"):
        if package in comparisons:
            data = comparisons[package]
            rates = []
            for mode, label in [("stock_vs_p6_cold", "stock versus Phase 6 cold"), ("p6_cold_vs_p6_zygote", "Phase 6 cold versus zygote")]:
                stats = data["modes"][mode]
                rates.append(f"{stats['matched']:,}/{stats['common_non_bv']:,} for {label}")
            build_lines.append(f"Archived {package} builds matched non-BV .olean hashes on " + " and ".join(rates) +
                               f". [Build comparison]({prefix}{data['source']})")
    verify = "\n".join(["## 10. Phase 6 verification", "", status, "", cpu_suffix, cpu_status, "", coverage, common, "",
        f"The corrected RX PNT replay processed {pnt['total_decls']:,} declarations with {pnt['gpu_rejected_count']} GPU rejections. "
        "Its earlier Phase 6 run recorded one GPU rejection for a missing sorryAx slot at declaration 540915. "
        f"[Targeted host and RX replay]({prefix}pnt_540915_replay/README.md)", "",
        f"The c7a tail and SageMaker used the corrected Linux verifier with SHA-256 \x60{cp['con_gpu_sha256']}\x60. "
        f"The two-root input archive SHA-256 was \x60{archive['sha256']}\x60. "
        f"Validated {sum(m['entries_checked'] for m in manifests)} receipt entries across {len(manifests)} manifests.", "", *build_lines, "", links])
    return bench, verify


def put(path, text):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8", newline="\n")
    tmp.replace(path)


def append_section(path, section):
    # Preserve the existing report bytes, including mixed historic line endings.
    raw = path.read_bytes()
    newline = b"\r\n" if b"\r\n" in raw else b"\n"
    start = b"<!-- generated Phase 6 metrics begin -->"
    end = b"<!-- generated Phase 6 metrics end -->"
    encoded = section.encode("utf-8").replace(b"\n", newline)
    block = start + newline + newline + encoded + newline + newline + end
    if start in raw or end in raw:
        require(raw.count(start) == raw.count(end) == 1, f"invalid Phase 6 markers in {path}")
        lo, hi = raw.index(start), raw.index(end)
        require(hi > lo, f"misordered Phase 6 markers in {path}")
        output = raw[:lo] + block + raw[hi + len(end):]
    else:
        padding = newline if raw.endswith(b"\n") else newline * 2
        output = raw + padding + b"---" + newline * 2 + block + newline
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_bytes(output)
    tmp.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase-dir", type=Path, default=HERE / "aws_ecosystem_phase6")
    parser.add_argument("--inventory-only", action="store_true", help="check available receipts and print row counts")
    parser.add_argument("--allow-pending-a10g", action="store_true", help="publish measured interim results while A10G is pending")
    args = parser.parse_args()
    root = args.phase_dir.resolve()
    manifests, indexed = check_manifests(root)
    rows = collect(root, indexed)
    if args.inventory_only:
        print(json.dumps(Counter(r["run"] for r in rows), indent=2))
        return
    archive = read(root / "shared_tail_inputs.json")
    cp = validate_cpu(rows, root, archive)
    candidates = ["nvidia_parity.json"]
    if args.allow_pending_a10g:
        candidates.append("l40s_parity.json")
    parity_path = next((root / name for name in candidates if (root / name).exists()), None)
    require(parity_path, "audited NVIDIA comparison receipt is required")
    parity = read(parity_path)
    require(parity["verifier_sha256"].lower() == cp["con_gpu_sha256"].lower(), "CPU and NVIDIA binaries differ")
    require(all(parity["input_archive_sha256"][p] == archive["sha256"] for p in TAIL), "CPU and NVIDIA inputs differ")
    verified_models = ["L40S"] if parity_path.name == "l40s_parity.json" else list(NVIDIA.values())
    if "A10G" not in verified_models:
        rows = [r for r in rows if r["platform"] != "A10G"]
    validate_nvidia_rows(root, rows, parity["verified_results"], verified_models)
    for p in TAIL:
        for model in verified_models:
            row = get_row(rows, p, model, "hybrid_cold")
            ref = get_row(rows, p, RX, "hybrid_cold")
            cpu = get_row(rows, p, CPU, "cpu_cold", 96)
            require(len({(r["total_decls"], r["verdict"], r["exit_code"]) for r in (ref, cpu, row)}) == 1,
                    f"fresh {model}, c7a and RX cold results differ for {p}")
            require(any(a["package"] == p and a["model"] == model and a["mode"] == "hybrid_cold"
                        and a["wall_ns"] == row["wall_ns"] and a["verdict"] == ref["verdict"]
                        and a["total_decls"] == ref["total_decls"] and a["gpu_rejected_count"] == 0
                        for a in parity["verified_results"]), f"missing audited {model}/{p} comparison")
    audit_path = root / "phase6_cpu_parity_audit.json"
    cpu_audit = read(audit_path) if audit_path.exists() else None
    if cpu_audit:
        require(not cpu_audit["problems"], f"CPU audit found discrepancies: {cpu_audit['problems']}")
    if parity_path.name == "nvidia_parity.json":
        require(cpu_audit and cpu_audit["complete"], "full publication requires the common CPU/GPU comparison receipt")
    comparisons = build_comparisons(root)
    corpus_path = root / "full_mathlib_corpus_comparison.json"
    corpus = read(corpus_path) if corpus_path.exists() else None
    bench, verify = report_sections(rows, cp, parity, manifests, archive, parity_path.name, cpu_audit, comparisons, corpus)
    master = {"phase": 6, "publication_status": "complete" if parity_path.name == "nvidia_parity.json" else "interim",
              "verified_nvidia_models": verified_models,
              "pending_nvidia_models": [m for m in NVIDIA.values() if m not in verified_models], "checksum_audit": manifests, "input_archive": archive,
              "cpu_tail_provenance": cp, "nvidia_comparison": {"source": parity_path.name, "sha256": digest(parity_path)},
              "common_cpu_comparison": {"source": audit_path.name, "sha256": digest(audit_path),
                                        "complete": cpu_audit["complete"]} if cpu_audit else None,
              "full_mathlib_corpus_comparison": {"source": corpus_path.name, "sha256": digest(corpus_path)} if corpus else None,
              "build_comparisons": comparisons, "measurements": rows}
    put(root / "phase6_metrics_master.json", json.dumps(master, indent=2) + "\n")
    path = root / "phase6_metrics_master.csv"
    tmp = path.with_suffix(".csv.tmp")
    with tmp.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    tmp.replace(path)
    append_section(root.parent / "ECOSYSTEM_BENCHMARK_REPORT.md", bench)
    append_section(root.parent / "VERIFICATION_REPORT.md", verify)
    print(f"Indexed {len(rows)} measured records and updated both Phase 6 reports.")


if __name__ == "__main__":
    main()

