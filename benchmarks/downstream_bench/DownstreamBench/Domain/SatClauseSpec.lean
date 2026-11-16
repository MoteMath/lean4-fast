import DownstreamBench.Verify.GrindCongruence
import DownstreamBench.Data.HashMapSpec

namespace DownstreamBench.Domain

abbrev Lit := Int
abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assign := Nat → Bool

def evalLit (a : Assign) (l : Lit) : Bool :=
  if l > 0 then a l.natAbs else if l < 0 then !(a l.natAbs) else false

def evalClause (a : Assign) (c : Clause) : Bool :=
  c.any (evalLit a)

def evalCNF (a : Assign) (f : CNF) : Bool :=
  f.all (evalClause a)

theorem evalClause_nil (a : Assign) : evalClause a [] = false := rfl

theorem evalClause_cons (a : Assign) (l : Lit) (c : Clause) :
    evalClause a (l :: c) = (evalLit a l || evalClause a c) := by
  simp [evalClause]

theorem evalCNF_nil (a : Assign) : evalCNF a [] = true := rfl

theorem evalCNF_cons (a : Assign) (c : Clause) (f : CNF) :
    evalCNF a (c :: f) = (evalClause a c && evalCNF a f) := by
  simp [evalCNF]

theorem empty_clause_implies_unsat (f : CNF) (hmem : [] ∈ f) (a : Assign) :
    evalCNF a f = false := by
  induction f with
  | nil => cases hmem
  | cons c cs ih =>
    simp only [List.mem_cons] at hmem
    cases hmem with
    | inl hc =>
      subst hc
      simp [evalCNF, evalClause]
    | inr hcs =>
      rw [evalCNF_cons, ih hcs]
      simp

theorem unit_prop_sound (a : Assign) (l : Lit) (c : Clause)
    (hc : evalClause a (l :: c) = true) (hfalse : evalLit a l = false) :
    evalClause a c = true := by
  rw [evalClause_cons, hfalse] at hc
  simpa using hc

end DownstreamBench.Domain
