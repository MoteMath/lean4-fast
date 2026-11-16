#!/usr/bin/env python3
"""Independent exact-integer reference LRAT/RUP verifier for Gate 2 fixtures."""
from pathlib import Path
import sys


def verify_lrat(cnf_path: Path, lrat_path: Path) -> tuple[bool, str]:
    clauses: dict[int, list[int]] = {}
    cid = 1
    for line in cnf_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line[0] in "pc":
            continue
        lits = [int(x) for x in line.split() if x != "0"]
        clauses[cid] = lits
        cid += 1

    has_empty = False
    for line in lrat_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("c"):
            continue
        if "d" in line.split():
            return False, "deletion line not expected in parallel LRAT fixture"
        nums = [int(x) for x in line.split()]
        sid = nums[0]
        if sid < cid:
            return False, f"non-increasing/colliding step id {sid} < {cid}"
        z1 = nums.index(0, 1)
        lits = nums[1:z1]
        z2 = nums.index(0, z1 + 1)
        hints = nums[z1 + 1 : z2]
        assign = {-l for l in lits}
        conflict = False
        for h in hints:
            if h <= 0 or h >= sid or h not in clauses:
                return False, f"invalid/non-causal hint {h} at step {sid}"
            unassigned = []
            sat = False
            for x in clauses[h]:
                if x in assign:
                    sat = True
                    break
                if -x not in assign:
                    unassigned.append(x)
            if sat:
                continue
            if len(unassigned) == 0:
                conflict = True
                break
            if len(unassigned) == 1:
                assign.add(unassigned[0])
            else:
                return False, f"non-unit hint {h} at step {sid}: {unassigned}"
        if not conflict:
            return False, f"no RUP conflict derived at step {sid}"
        clauses[sid] = lits
        if not lits:
            has_empty = True
    if not has_empty:
        return False, "missing empty clause"
    return True, "OK"


def main():
    d = Path(__file__).resolve().parent / "lrat_fixtures"
    cases = [
        ("valid_unsat.cnf", "valid_unsat.lrat", True),
        ("chain_500_valid.cnf", "chain_500_valid.lrat", True),
        ("chain_500_valid.cnf", "chain_500_multistep_valid.lrat", True),
        ("valid_unsat.cnf", "bad_wrong_derived_lit.lrat", False),
        ("valid_unsat.cnf", "bad_no_empty_clause.lrat", False),
        ("valid_unsat.cnf", "bad_noncausal_hint.lrat", False),
        ("valid_unsat.cnf", "bad_self_hint.lrat", False),
        ("valid_unsat.cnf", "bad_missing_hints.lrat", False),
        ("valid_unsat.cnf", "bad_bogus_empty.lrat", False),
        ("chain_500_valid.cnf", "chain_500_bad_broken_link.lrat", False),
    ]
    failed = 0
    for cnf_n, lrat_n, expect in cases:
        ok, msg = verify_lrat(d / cnf_n, d / lrat_n)
        status = "PASS" if ok == expect else "FAIL"
        if ok != expect:
            failed += 1
        print(f"[{status}] {lrat_n}: ok={ok} (expect={expect}) -> {msg}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
