import DownstreamBench.Prelude

namespace DownstreamBench.Verify

open DownstreamBench

def simplifyOnce : SymExpr → SymExpr
  | .neg (.lit k) => .lit (-k)
  | .neg (.neg e) => e
  | .add (.lit 0) b => b
  | .add a (.lit 0) => a
  | .add (.lit a) (.lit b) => .lit (a + b)
  | .mul (.lit 0) _ => .lit 0
  | .mul _ (.lit 0) => .lit 0
  | .mul (.lit 1) b => b
  | .mul a (.lit 1) => a
  | .mul (.lit a) (.lit b) => .lit (a * b)
  | e => e

def simplifySym : SymExpr → SymExpr
  | .lit k => .lit k
  | .var i => .var i
  | .neg e => simplifyOnce (.neg (simplifySym e))
  | .add a b => simplifyOnce (.add (simplifySym a) (simplifySym b))
  | .mul a b => simplifyOnce (.mul (simplifySym a) (simplifySym b))

@[simp] theorem simplifyOnce_eval (env : Nat → Int) (e : SymExpr) :
    (simplifyOnce e).eval env = e.eval env := by
  cases e with
  | lit _ => rfl
  | var _ => rfl
  | neg x =>
    cases x <;> simp [simplifyOnce, Int.neg_neg]
  | add a b =>
    cases a with
    | lit ka =>
      cases b with
      | lit kb =>
        by_cases ha : ka = 0 <;> by_cases hb : kb = 0 <;> simp [simplifyOnce, ha, hb]
      | _ =>
        by_cases ha : ka = 0 <;> simp [simplifyOnce, ha]
    | _ =>
      cases b with
      | lit kb =>
        by_cases hb : kb = 0 <;> simp [simplifyOnce, hb]
      | _ => rfl
  | mul a b =>
    cases a with
    | lit ka =>
      cases b with
      | lit kb =>
        by_cases ha0 : ka = 0 <;> by_cases ha1 : ka = 1 <;>
          by_cases hb0 : kb = 0 <;> by_cases hb1 : kb = 1 <;>
          simp [simplifyOnce, ha0, ha1, hb0, hb1]
      | _ =>
        by_cases ha0 : ka = 0 <;> by_cases ha1 : ka = 1 <;> simp [simplifyOnce, ha0, ha1]
    | _ =>
      cases b with
      | lit kb =>
        by_cases hb0 : kb = 0 <;> by_cases hb1 : kb = 1 <;> simp [simplifyOnce, hb0, hb1]
      | _ => rfl

@[simp] theorem simplifySym_eval (env : Nat → Int) (e : SymExpr) :
    (simplifySym e).eval env = e.eval env := by
  induction e <;> simp [simplifySym, *]

theorem simp_cascade_poly (env : Nat → Int) :
    (simplifySym (SymExpr.add
      (SymExpr.mul (.lit 1) (.add (.var 0) (.lit 0)))
      (SymExpr.add (.neg (.neg (.var 1))) (.mul (.lit 0) (.var 2))))).eval env =
      env 0 + env 1 := by
  simp

theorem simp_cascade_nested (env : Nat → Int) (k : Int) :
    (simplifySym (SymExpr.mul (.add (.lit 2) (.lit (-1))) (.add (.var 0) (.lit k)))).eval env =
      env 0 + k := by
  simp

end DownstreamBench.Verify
