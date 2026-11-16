import DownstreamBench.Verify.SimpRewriteBank
import DownstreamBench.Verify.OmegaStress

namespace DownstreamBench.Domain

open DownstreamBench

inductive VMInstr where
  | push : Int → VMInstr
  | load : Nat → VMInstr
  | neg : VMInstr
  | add : VMInstr
  | mul : VMInstr
  deriving Repr, DecidableEq

def vmStep (env : Nat → Int) (stk : List Int) : VMInstr → List Int
  | .push k => k :: stk
  | .load i => env i :: stk
  | .neg => match stk with
    | x :: rest => (-x) :: rest
    | [] => []
  | .add => match stk with
    | b :: a :: rest => (a + b) :: rest
    | _ => stk
  | .mul => match stk with
    | b :: a :: rest => (a * b) :: rest
    | _ => stk

def vmRun (env : Nat → Int) (prog : List VMInstr) (stk : List Int) : List Int :=
  prog.foldl (vmStep env) stk

theorem vmRun_append (env : Nat → Int) (p₁ p₂ : List VMInstr) (stk : List Int) :
    vmRun env (p₁ ++ p₂) stk = vmRun env p₂ (vmRun env p₁ stk) := by
  simp [vmRun, List.foldl_append]

def compileSym : SymExpr → List VMInstr
  | .lit k => [.push k]
  | .var i => [.load i]
  | .neg e => compileSym e ++ [.neg]
  | .add a b => compileSym a ++ compileSym b ++ [.add]
  | .mul a b => compileSym a ++ compileSym b ++ [.mul]

theorem compileSym_correct (env : Nat → Int) (e : SymExpr) (stk : List Int) :
    vmRun env (compileSym e) stk = e.eval env :: stk := by
  induction e generalizing stk with
  | lit k => rfl
  | var i => rfl
  | neg e ih =>
    simp only [compileSym, vmRun_append, ih]
    rfl
  | add a b iha ihb =>
    simp only [compileSym, vmRun_append, iha, ihb]
    rfl
  | mul a b iha ihb =>
    simp only [compileSym, vmRun_append, iha, ihb]
    rfl

theorem compileSym_simplify_equiv (env : Nat → Int) (e : SymExpr) :
    vmRun env (compileSym (Verify.simplifySym e)) [] = [e.eval env] := by
  rw [compileSym_correct, Verify.simplifySym_eval]

end DownstreamBench.Domain
