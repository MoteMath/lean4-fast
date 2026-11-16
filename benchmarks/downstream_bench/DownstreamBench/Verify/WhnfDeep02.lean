import DownstreamBench.Algebra.LatticeTheory
import DownstreamBench.Logic.TermSyntax

namespace DownstreamBench.Verify

def Church (α : Type u) := (α → α) → α → α

def cZero : Church α := fun _ x => x
def cSucc (n : Church α) : Church α := fun f x => f (n f x)
def cAdd (m n : Church α) : Church α := fun f x => m f (n f x)
def cMul (m n : Church α) : Church α := fun f => m (n f)

def cTwo : Church α := cSucc (cSucc cZero)
def cThree : Church α := cSucc cTwo
def cFive : Church α := cAdd cTwo cThree
def cSix : Church α := cMul cTwo cThree

theorem church_two_plus_three_eq (α : Type u) (f : α → α) (x : α) :
    cFive f x = f (f (f (f (f x)))) := rfl

theorem church_two_mul_three_eq (α : Type u) (f : α → α) (x : α) :
    cSix f x = f (f (f (f (f (f x))))) := rfl

theorem church_add_comm_concrete (α : Type u) (f : α → α) (x : α) :
    cAdd cTwo cThree f x = cAdd cThree cTwo f x := rfl

theorem church_mul_dist_concrete (α : Type u) (f : α → α) (x : α) :
    cMul cTwo (cAdd cTwo cThree) f x = cAdd (cMul cTwo cTwo) (cMul cTwo cThree) f x := rfl

theorem church_eval_nat (k : Nat) :
    cSix (· + 2) (cFive (· + 1) k) = k + 17 := by
  dsimp [cSix, cFive, cTwo, cThree, cAdd, cMul, cSucc, cZero]

theorem church_eval_bitvec (v : BitVec 16) :
    cFive (· + 1#16) (cTwo (· + 2#16) v) = v + 9#16 := by
  dsimp [cFive, cTwo, cThree, cAdd, cSucc, cZero]
  bv_decide

theorem lam_shift_nested (a b c : Nat) (t₁ t₂ : Logic.LamTerm) :
    (Logic.LamTerm.app (.lam (.base a) t₁) (.pair (.var b) (.lam (.base c) t₂))).shift 0 0 =
      .app (.lam (.base a) t₁) (.pair (.var b) (.lam (.base c) t₂)) := by
  simp

end DownstreamBench.Verify
