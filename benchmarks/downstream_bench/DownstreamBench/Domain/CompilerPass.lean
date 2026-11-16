import DownstreamBench.Verify.SimpRewriteBank
import DownstreamBench.Verify.GrindCongruence

namespace DownstreamBench.Domain

open DownstreamBench

inductive MiniStmt where
  | skip : MiniStmt
  | assign : Nat → SymExpr → MiniStmt
  | seq : MiniStmt → MiniStmt → MiniStmt
  | ifPos : SymExpr → MiniStmt → MiniStmt → MiniStmt
  deriving Repr, DecidableEq

def MiniStmt.exec (s : MiniStmt) (env : Nat → Int) : Nat → Int :=
  match s with
  | .skip => env
  | .assign x e => fun y => if y == x then e.eval env else env y
  | .seq a b => b.exec (a.exec env)
  | .ifPos cond t f => if cond.eval env > 0 then t.exec env else f.exec env

def MiniStmt.dce : MiniStmt → MiniStmt
  | .skip => .skip
  | .assign x e => .assign x (Verify.simplifySym e)
  | .seq .skip b => b.dce
  | .seq a .skip => a.dce
  | .seq a b => .seq a.dce b.dce
  | .ifPos c t f => .ifPos (Verify.simplifySym c) t.dce f.dce

theorem MiniStmt.dce_seq_exec (a b : MiniStmt) (env : Nat → Int) :
    (MiniStmt.seq a b).dce.exec env = b.dce.exec (a.dce.exec env) := by
  cases a <;> cases b <;> rfl

theorem MiniStmt.dce_sound (s : MiniStmt) (env : Nat → Int) :
    s.dce.exec env = s.exec env := by
  induction s generalizing env with
  | skip => rfl
  | assign x e =>
    funext y
    simp [MiniStmt.dce, MiniStmt.exec]
  | seq a b iha ihb =>
    rw [MiniStmt.dce_seq_exec, iha, ihb]
    rfl
  | ifPos c t f iht ihf =>
    simp only [MiniStmt.dce, MiniStmt.exec, Verify.simplifySym_eval]
    split <;> simp [*]

theorem dce_seq_skip_left (s : MiniStmt) (env : Nat → Int) :
    (MiniStmt.seq .skip s).dce.exec env = s.exec env := by
  rw [MiniStmt.dce_sound]
  rfl

end DownstreamBench.Domain
