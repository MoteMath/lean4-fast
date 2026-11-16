import DownstreamBench.Prelude

namespace DownstreamBench.Algebra

theorem mpow_add [BenchMonoid α] (x : α) (m n : Nat) :
    mpow x (m + n) = BenchMagma.mul (mpow x m) (mpow x n) := by
  induction m with
  | zero =>
    simp [mpow, BenchMonoid.one_mul]
  | succ m ih =>
    rw [Nat.succ_add, mpow_succ, mpow_succ, ih, BenchSemigroup.mul_assoc]

theorem mpow_comm_mul [BenchCommMonoid α] (x y : α) (n : Nat) :
    mpow (BenchMagma.mul x y) n = BenchMagma.mul (mpow x n) (mpow y n) := by
  induction n with
  | zero =>
    simp [mpow, BenchMonoid.one_mul]
  | succ n ih =>
    rw [mpow_succ, mpow_succ, mpow_succ, ih]
    calc BenchMagma.mul (BenchMagma.mul x y) (BenchMagma.mul (mpow x n) (mpow y n))
        = BenchMagma.mul x (BenchMagma.mul y (BenchMagma.mul (mpow x n) (mpow y n))) := by
          rw [BenchSemigroup.mul_assoc]
      _ = BenchMagma.mul x (BenchMagma.mul (BenchMagma.mul y (mpow x n)) (mpow y n)) := by
          rw [← BenchSemigroup.mul_assoc y (mpow x n) (mpow y n)]
      _ = BenchMagma.mul x (BenchMagma.mul (BenchMagma.mul (mpow x n) y) (mpow y n)) := by
          rw [BenchCommMonoid.mul_comm y (mpow x n)]
      _ = BenchMagma.mul x (BenchMagma.mul (mpow x n) (BenchMagma.mul y (mpow y n))) := by
          rw [BenchSemigroup.mul_assoc (mpow x n) y (mpow y n)]
      _ = BenchMagma.mul (BenchMagma.mul x (mpow x n)) (BenchMagma.mul y (mpow y n)) := by
          rw [← BenchSemigroup.mul_assoc x (mpow x n)]

/-- Deep open-term WHNF identities under 8+ nested binders (no local `let` decls). -/
theorem open_whnf_monoid_chain (a b c d e f g h : Nat) :
    iterApply (fun z => z + 1) 4 (a + b + c + d + e + f + g + h) =
      a + b + c + d + e + f + g + h + 4 := by
  simp [iterApply]

theorem open_whnf_prod_mpow (a b : Nat) (x y : BitVec 32) :
    mpow ((a + b, x ^^^ y) : Nat × BitVec 32) 3 =
      ((a + b) + ((a + b) + ((a + b) + 0)), (x ^^^ y) + ((x ^^^ y) + ((x ^^^ y) + 0#32))) := by
  rfl

theorem semiring_sq_expand [BenchSemiring α] (x y : α) :
    BenchSemiring.mul (BenchSemiring.add x y) (BenchSemiring.add x y) =
      BenchSemiring.add
        (BenchSemiring.add (BenchSemiring.mul x x) (BenchSemiring.mul x y))
        (BenchSemiring.add (BenchSemiring.mul y x) (BenchSemiring.mul y y)) := by
  rw [BenchSemiring.left_distrib, BenchSemiring.right_distrib, BenchSemiring.right_distrib]
  rw [BenchSemiring.add_assoc (BenchSemiring.mul x x)]
  rw [← BenchSemiring.add_assoc (BenchSemiring.mul y x) (BenchSemiring.mul x y)]
  rw [BenchSemiring.add_comm (BenchSemiring.mul y x) (BenchSemiring.mul x y)]
  rw [BenchSemiring.add_assoc (BenchSemiring.mul x y) (BenchSemiring.mul y x)]
  rw [← BenchSemiring.add_assoc (BenchSemiring.mul x x)]

end DownstreamBench.Algebra
