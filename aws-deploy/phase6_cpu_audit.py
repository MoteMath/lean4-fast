"""Audit the Phase 6 c7a matrix and cross-platform cold shared-input outcomes."""
import argparse
import hashlib
import json
from pathlib import Path

TAGS = {"Aesop":"aesop", "Batteries":"batteries", "Cedar":"cedar", "DocGen4":"doc_gen4",
        "DownstreamBench":"downstream_bench", "DownstreamReal":"downstream_real",
        "Full_Mathlib":"full_mathlib", "ImportGraph":"import_graph", "Init_Std":"Init_Std",
        "Mathlib_Real_Basic":"Mathlib_Real_Basic", "Plausible":"plausible",
        "PrimeNumberTheoremAnd":"PrimeNumberTheoremAnd", "Qq":"qq", "SyntheticBench":"synthetic"}
TAIL = {"Full_Mathlib", "PrimeNumberTheoremAnd"}
DECLINED = {"Cedar", "PrimeNumberTheoremAnd"}

def sha(path):
    h=hashlib.sha256()
    with path.open("rb") as source:
        for data in iter(lambda:source.read(1<<20),b""):
            h.update(data)
    return h.hexdigest()

def audit(base):
    missing, problems = [], []
    historic = base / "cpu_c7a_96vcpu"
    tail = base / "cpu_c7a_96vcpu_tail"
    c7a = base / "cpu_c7a_96vcpu_common"
    rx = base / "local_rx7900xtx"
    rx_extra = base / "local_rx7900xtx_supplement"
    def records(dirs, name, optional=False):
        files = sorted({p for d in dirs if d.is_dir() for p in d.rglob(name)})
        if not files and not optional:
            missing.append("|".join(str(x.relative_to(base)) for x in dirs)+"/"+name)
        rows = []
        for p in files:
            with p.open(encoding="utf-8-sig") as f:
                rows.append((str(p.relative_to(base)), json.load(f)))
        return rows
    def truth(pkg, source, row, *, backend, threads=None):
        code = 2 if pkg in DECLINED else 0
        expected = {"exit_code":code, "verdict":"Declined" if code else "Accepted",
                    "backend_mode":backend, "prefix_skipped":0}
        if threads:
            expected["threads"] = threads
        if backend == "hybrid":
            expected["gpu_rejected_count"] = 0
            if row.get("gpu_verified_count", 0) <= 0:
                problems.append(f"{source}: no GPU verified jobs")
        for field, val in expected.items():
            if row.get(field) != val:
                problems.append(f"{source}: {field}={row.get(field)!r}, expected {val!r}")
        if row.get("total_decls", 0) <= 0:
            problems.append(f"{source}: no verified stream count")
        return (row.get("total_decls"), row.get("verdict"), row.get("exit_code"))
    native = {}
    for pkg, tag in TAGS.items():
        ds = [tail] if pkg in TAIL else [historic]
        stock = "real_basic" if pkg == "Mathlib_Real_Basic" else tag
        stock_rows = records(ds, stock + "_stock_leanchecker.json")
        for p, row in stock_rows:
            if row.get("exit_code") != 0 or "--fresh" not in str(row.get("cmd")):
                problems.append(f"{p}: missing successful stock --fresh check")
        receipts={}
        seen=set()
        for mode in (["cold"] if pkg in DECLINED else ["cold","snap"]):
            for t in (96,48,16):
                key=f"{mode}_{t}t"
                receipts[key]=[]
                for p,row in records(ds,f"{tag}_congpu_{key}.json"):
                    sig=truth(pkg,p,row,backend="cpu",threads=t)
                    seen.add(sig)
                    receipts[key].append(p)
        if len(seen)>1: problems.append(f"{pkg}: c7a CPU modes disagree {seen}")
        native[pkg]={"input_cohort":"reconstructed_shared" if pkg in TAIL else "archived_c7a_native_build", "stock":[p for p,_ in stock_rows], "modes":receipts,
                     "declarations":next(iter(seen))[0] if len(seen)==1 else None}
    common={}
    for pkg in TAGS.keys()-{"DownstreamReal"}:
        expected_counts=set()
        cpu = (records([tail],f"{TAGS[pkg]}_congpu_cold_96t.json") if pkg in TAIL
               else records([c7a,tail/"shared_cpu_96t"],pkg+"_cpu_cold.json"))
        sets = {"c7a_cpu":(cpu,"cpu"),
                "rx_hybrid":((records([base/"pnt_540915_replay"],"rx_full.json") if pkg=="PrimeNumberTheoremAnd"
                              else records([rx_extra],pkg+"_hybrid_cold.json",True)
                              or records([rx],pkg+"_hybrid_cold.json")),"hybrid")}
        for gpu,folder in (("l40s","gpu_l40s_g6e"),("a10g","gpu_a10g_g5")):
            for mode in ("cpu","hybrid"):
                sets[gpu+"_"+mode]=(records([base/folder],f"{pkg}_{mode}_cold.json"),mode)
        result={}
        for platform,(rows,backend) in sets.items():
            for p,row in rows:
                sig=truth(pkg,p,row,backend=backend,threads=96 if platform=="c7a_cpu" else None)
                expected_counts.add(sig)
            result[platform]=[p for p,_ in rows]
        if len(expected_counts)>1:
            problems.append(f"{pkg}: shared-input outcomes differ {sorted(expected_counts)}")
        common[pkg]={"shared_outcomes":[list(s) for s in sorted(expected_counts)],
                     "cpu_scaling_declarations":native[pkg]["declarations"], "cpu_scaling_input":native[pkg]["input_cohort"], "sources":result}
    integrity={}
    for folders, name in (([historic],"sha256sums.txt"),([tail],"tail_sha256sums.txt"),
                          ([c7a,tail/"shared_cpu_96t"],"sha256sums.txt")):
        manifests=sorted({p for folder in folders if folder.exists() for p in folder.rglob(name)})
        if not manifests:
            missing.append(str(folders[0].relative_to(base)/name))
        for mf in manifests:
            checked=0
            for line in mf.read_text(encoding="utf-8-sig").splitlines():
                digest, rel = line.split(maxsplit=1)
                path=(mf.parent/rel.lstrip("*")).resolve()
                if mf.parent not in path.parents or not path.is_file() or sha(path)!=digest.lower():
                    problems.append(f"{mf.name}: invalid digest or absent file {rel}")
                else:
                    checked += 1
            integrity[str(mf.relative_to(base))]=checked
    cohorts={}
    prior=list(tail.rglob("initial_count_check/full_mathlib_congpu_cold_96t.json.part"))
    official=records([tail],"full_mathlib_congpu_cold_96t.json",True)
    if not prior:
        missing.append("cpu_c7a_96vcpu_tail/initial_count_check/full_mathlib_congpu_cold_96t.json.part")
    elif official:
        official_path=base/official[0][0]
        for filename in ("full_mathlib_congpu_cold_96t.json", "full_mathlib_congpu_cold_96t.log"):
            raw=prior[0].parent/(filename+".part")
            final=official_path.parent/filename
            if not raw.is_file() or not final.is_file() or sha(raw)!=sha(final):
                problems.append(f"Initial CPU checkpoint differs from promoted {filename}")
        if not problems: cohorts["initial_cold_checkpoint_matches_promoted_receipt"]=True
    refs=records([tail],"full_mathlib_reference.json")
    if refs:
        ref_path=base/refs[0][0]
        cohort_path=ref_path.with_name("tail_provenance.json")
        if not cohort_path.is_file():
            missing.append(str(cohort_path.relative_to(base)))
        else:
            meta=json.loads(cohort_path.read_text())["full_mathlib_cohort"]
            if (meta.get("reference_sha256")!=sha(ref_path) or meta.get("reference_decl_count")!=refs[0][1]["total_decls"]
                    or meta.get("historical_rx_decl_count")!=775326):
                problems.append("Full Mathlib CPU provenance does not bind the reference/historical counts")
            cohorts.update(meta)
        rx_ref=rx_extra/"Full_Mathlib_hybrid_cold.json"
        if rx_ref.is_file():
            rxrow=json.loads(rx_ref.read_text())
            if refs[0][1]["total_decls"]!=rxrow["total_decls"]:
                problems.append("Fresh RX disagrees with count used by c7a cohort")
            cohorts["shared_rx_sha256"]=sha(rx_ref)
            cohorts["shared_rx_decl_count"]=rxrow["total_decls"]
    shared={}
    root_records=records([base/"supplement_input_audit"],"phase6_11_roots.json")
    common_provs=records([c7a,tail/"shared_cpu_96t"],"shared_cpu_provenance.json")
    if common_provs and root_records:
        expected_inputs=root_records[0][1]
        for prov_path, prov in common_provs:
            observed_roots={}
            for pkg, package in expected_inputs.items():
                roots={r["path"].removeprefix("../"):r["sha256"] for r in package["roots"]}
                actual=prov["inputs"].get(pkg,{})
                if actual.get("roots_sha256")!=roots:
                    problems.append(f"{prov_path}: c7a input hashes differ for {pkg}")
                observed_roots[pkg]=actual.get("roots_sha256",{})
            if prov["inputs"].get("ImportGraph",{}).get("manifest_sha256")!="3fc9372c8d0a387f9e194b8a065e708725d78dc824e1bfdc219f99dcced14d9d":
                problems.append(f"{prov_path}: c7a did not use deduplicated ImportGraph load paths")
            shared[prov_path]=observed_roots
    cpu_missing=[p for p in missing if not p.startswith(("gpu_","local_rx"))]
    cpu_problem=[p for p in problems if not any(w in p for w in ("gpu_l40s","gpu_a10g","local_rx","shared-input outcomes differ"))]
    cpu_summary={"complete":not cpu_missing and not cpu_problem,
                 "stock_records":sum(len(r["stock"]) for r in native.values()),
                 "scaling_records":sum(len(paths) for r in native.values() for paths in r["modes"].values()),
                 "shared_cold_96t":sum(bool(row["sources"]["c7a_cpu"]) for row in common.values())}
    return {"cpu_summary":cpu_summary,"shared_root_hashes":shared,"cpu_sha256":integrity,"full_mathlib_cohort":cohorts,"complete":not missing and not problems, "missing":sorted(missing),
            "problems":problems, "cpu_scaling":native, "common_cold_parity":common}

if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory",type=Path)
    parser.add_argument("--json",type=Path)
    args=parser.parse_args()
    report=audit(args.directory.resolve())
    if args.json:
        args.json.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in ("complete","missing","problems")},indent=2))
    raise SystemExit(0 if report["complete"] else 2)


