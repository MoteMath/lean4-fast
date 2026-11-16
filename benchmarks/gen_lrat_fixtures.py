#!/usr/bin/env python3
"""
Generate valid UNSAT DIMACS CNF + causal LRAT proofs and mutated adversarial
LRAT / .olean fixtures for Gate 2 soundness verification.
"""
from pathlib import Path

OUT = Path(__file__).resolve().parent / "lrat_fixtures"
OUT.mkdir(parents=True, exist_ok=True)

# 1. Valid UNSAT CNF (p cnf 3 6) + valid causal LRAT proof
# Clauses:
# 1:  1  2 0
# 2:  1 -2 0
# 3: -1  3 0
# 4: -1 -3 0
# 5: (derived 5)  1 0   via hints [1, 2]   (negating 1 gives -1; C1 gives 2, C2 gives -2 -> conflict)
# 6: (derived 6) -1 0   via hints [3, 4]   (negating -1 gives 1; C3 gives 3, C4 gives -3 -> conflict)
# 7: (derived 7)  0     via hints [5, 6]   (empty clause from unit 1 and unit -1)
VALID_CNF = """p cnf 3 4
1 2 0
1 -2 0
-1 3 0
-1 -3 0
"""
VALID_LRAT = """5 1 0 1 2 0
6 -1 0 3 4 0
7 0 5 6 0
"""

(OUT / "valid_unsat.cnf").write_text(VALID_CNF, encoding="utf-8")
(OUT / "valid_unsat.lrat").write_text(VALID_LRAT, encoding="utf-8")

# Adversarial LRAT mutations (ALL MUST BE REJECTED):
# A) Bogus derived literal (claims 2 instead of 1 with hints [1, 2])
(OUT / "bad_wrong_derived_lit.lrat").write_text(
    "5 2 0 1 2 0\n6 -1 0 3 4 0\n7 0 5 6 0\n", encoding="utf-8"
)

# B) Missing empty clause (stops before deriving 0)
(OUT / "bad_no_empty_clause.lrat").write_text(
    "5 1 0 1 2 0\n6 -1 0 3 4 0\n", encoding="utf-8"
)

# C) Non-causal forward hint (step 5 references step 6 >= 5!)
(OUT / "bad_noncausal_hint.lrat").write_text(
    "5 1 0 1 6 0\n6 -1 0 3 4 0\n7 0 5 6 0\n", encoding="utf-8"
)

# D) Self-referential hint (step 5 references 5)
(OUT / "bad_self_hint.lrat").write_text(
    "5 1 0 5 2 0\n6 -1 0 3 4 0\n7 0 5 6 0\n", encoding="utf-8"
)

# E) Insufficient hints (empty hint list for step 5, not RUP)
(OUT / "bad_missing_hints.lrat").write_text(
    "5 1 0 0\n6 -1 0 3 4 0\n7 0 5 6 0\n", encoding="utf-8"
)

# F) Unsound empty clause directly from initial non-conflicting clauses
(OUT / "bad_bogus_empty.lrat").write_text(
    "5 0 1 3 0\n", encoding="utf-8"
)

# 2. Larger valid UNSAT CNF: XOR-chain contradiction (N=200 vars, linear chain parity contradiction)
# Actually let's generate a 64-bit / 100-var Tseitin parity / implication chain with exact LRAT proof:
# Chain of units: x1, (¬x1 ∨ x2), (¬x2 ∨ x3), ..., (¬x_{n-1} ∨ x_n), ¬x_n
N = 500
cnf_lines = [f"p cnf {N} {N + 1}"]
cnf_lines.append("1 0")  # clause 1: x1
for i in range(1, N):
    cnf_lines.append(f"{-i} {i + 1} 0")  # clause i+1: -x_i \/ x_{i+1}
cnf_lines.append(f"{-N} 0")  # clause N+1: -x_N
(OUT / "chain_500_valid.cnf").write_text("\n".join(cnf_lines) + "\n", encoding="utf-8")

# Derive empty clause using sequential RUP chain:
# Wait: for parallel LRAT (causal hints j < k), if step N+2 derives empty clause directly with hints 1,2,...,N+1:
lrat_chain_all = [f"{N + 2} 0 " + " ".join(str(c) for c in range(1, N + 2)) + " 0"]
(OUT / "chain_500_valid.lrat").write_text("\n".join(lrat_chain_all) + "\n", encoding="utf-8")

# Multi-step causal LRAT for chain_500:
# Step N+2: x_2 via [1, 2]
# Step N+3: x_3 via [N+2, 3]
# ...
# Step 2N: x_N via [2N-1, N]
# Step 2N+1: empty via [2N, N+1]
lrat_multi = []
prev_unit_id = 1
for i in range(2, N + 1):
    step_id = N + i
    clause_impl_id = i
    lrat_multi.append(f"{step_id} {i} 0 {prev_unit_id} {clause_impl_id} 0")
    prev_unit_id = step_id
lrat_multi.append(f"{2 * N + 1} 0 {prev_unit_id} {N + 1} 0")
(OUT / "chain_500_multistep_valid.lrat").write_text("\n".join(lrat_multi) + "\n", encoding="utf-8")

# Corrupted chain_500 (drops middle link clause N/2 from hints!)
bad_hints = [str(c) for c in range(1, N + 2) if c != (N // 2)]
(OUT / "chain_500_bad_broken_link.lrat").write_text(
    f"{N + 2} 0 " + " ".join(bad_hints) + " 0\n", encoding="utf-8"
)

print(f"Generated LRAT fixtures in {OUT}")
