import DownstreamBench.Algebra.MonoidLaws
import DownstreamBench.Data.TreeStructures

namespace DownstreamBench.Verify

open DownstreamBench

/-- Deep open-term arithmetic pipeline evaluated under many universal binders without local let-decls. -/
def openFoldStep (k : Nat) (x y z : Nat) : Nat :=
  match k with
  | 0 => x + y + z
  | n + 1 => openFoldStep n (x + 1) (y + 2) (z + 3)

@[simp] theorem openFoldStep_eq (k x y z : Nat) :
    openFoldStep k x y z = x + y + z + 6 * k := by
  induction k generalizing x y z with
  | zero => simp [openFoldStep]
  | succ n ih =>
    simp [openFoldStep, ih]
    omega

theorem open_whnf_fold_6 (a b c d e f : Nat) :
    openFoldStep 6 (a + b) (c + d) (e + f) = (a + b) + (c + d) + (e + f) + 36 := by
  simp

theorem open_whnf_fold_8 (a b c d e f g h : Nat) :
    openFoldStep 8 (a + b + c) (d + e) (f + g + h) =
      (a + b + c) + (d + e) + (f + g + h) + 48 := by
  simp

theorem open_whnf_iter_add_1 (x₀ x₁ x₂ x₃ x₄ x₅ : Nat) :
    iterApply (fun v => v + 3) 5 (x₀ + x₁ + x₂ + x₃ + x₄ + x₅) =
      x₀ + x₁ + x₂ + x₃ + x₄ + x₅ + 15 := by
  simp [iterApply]

theorem open_whnf_iter_add_2 (x₀ x₁ x₂ x₃ x₄ x₅ : Nat) :
    iterApply (fun v => v + 3) 7 (x₀ + x₁ + x₂ + x₃ + x₄ + x₅) =
      x₀ + x₁ + x₂ + x₃ + x₄ + x₅ + 21 := by
  simp [iterApply]

theorem open_whnf_iter_compose (f : Nat → Nat) (a b c d : Nat) :
    iterApply f 3 (iterApply f 2 (a + b + c + d)) = iterApply f 5 (a + b + c + d) := by
  rw [← iterApply_add]

theorem open_whnf_tree_mirror (l r : Data.BTree Nat) (x y : Nat) :
    (Data.BTree.node (.node l x r) y (.node r x l)).mirror.size = 3 + 2 * l.size + 2 * r.size := by
  simp [Data.BTree.size]
  omega

/-- Local `let` binding soundness test: zeta-reduction MUST reflect updated let-value in open context! -/
theorem local_let_zeta_sound (a b : Nat) :
    let u := a + b
    let v := u + 5
    iterApply (fun z => z + 1) 3 v = a + b + 8 := by
  intro u v
  simp [u, v, iterApply]

end DownstreamBench.Verify
