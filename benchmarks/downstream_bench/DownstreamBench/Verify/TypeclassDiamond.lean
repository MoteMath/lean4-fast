import DownstreamBench.Algebra.MonoidLaws
import DownstreamBench.Data.HashMapSpec

namespace DownstreamBench.Verify

open DownstreamBench

structure Tagged (tag : Nat) (α : Type u) where
  val : α
  deriving Repr, DecidableEq, Hashable

instance (tag : Nat) [BenchMagma α] : BenchMagma (Tagged tag α) where
  mul a b := ⟨BenchMagma.mul a.val b.val⟩

instance (tag : Nat) [BenchSemigroup α] : BenchSemigroup (Tagged tag α) where
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp [BenchMagma.mul, BenchSemigroup.mul_assoc]

instance (tag : Nat) [BenchMonoid α] : BenchMonoid (Tagged tag α) where
  one := ⟨BenchMonoid.one⟩
  one_mul a := by
    cases a
    simp [BenchMagma.mul, BenchMonoid.one_mul]
  mul_one a := by
    cases a
    simp [BenchMagma.mul, BenchMonoid.mul_one]

instance (tag : Nat) [BenchCommMonoid α] : BenchCommMonoid (Tagged tag α) where
  mul_comm a b := by
    cases a; cases b
    change Tagged.mk (BenchMagma.mul _ _) = Tagged.mk (BenchMagma.mul _ _)
    rw [BenchCommMonoid.mul_comm]

structure Mat2 (α : Type u) where
  m00 : α
  m01 : α
  m10 : α
  m11 : α
  deriving Repr, DecidableEq, Hashable

def Mat2.add [BenchSemiring α] (A B : Mat2 α) : Mat2 α :=
  ⟨BenchSemiring.add A.m00 B.m00, BenchSemiring.add A.m01 B.m01,
   BenchSemiring.add A.m10 B.m10, BenchSemiring.add A.m11 B.m11⟩

def Mat2.mul [BenchSemiring α] (A B : Mat2 α) : Mat2 α :=
  ⟨BenchSemiring.add (BenchSemiring.mul A.m00 B.m00) (BenchSemiring.mul A.m01 B.m10),
   BenchSemiring.add (BenchSemiring.mul A.m00 B.m01) (BenchSemiring.mul A.m01 B.m11),
   BenchSemiring.add (BenchSemiring.mul A.m10 B.m00) (BenchSemiring.mul A.m11 B.m10),
   BenchSemiring.add (BenchSemiring.mul A.m10 B.m01) (BenchSemiring.mul A.m11 B.m11)⟩

theorem tagged_nested_mpow (x : Tagged 1 (Tagged 2 (Tagged 3 Nat))) :
    mpow x 2 = BenchMagma.mul x (BenchMagma.mul x BenchMonoid.one) := rfl

theorem tagged_diamond_comm (x y : Tagged 7 (Tagged 11 (Nat × BitVec 32))) :
    BenchMagma.mul x y = BenchMagma.mul y x :=
  BenchCommMonoid.mul_comm x y

theorem mat2_add_comm [BenchSemiring α] (A B : Mat2 α) :
    Mat2.add A B = Mat2.add B A := by
  cases A; cases B
  simp [Mat2.add, BenchSemiring.add_comm]

theorem tagged_hashmap_synth (m : Std.HashMap (Tagged 5 (Nat × Nat)) Nat)
    (k : Tagged 5 (Nat × Nat)) (v : Nat) :
    (m.insert k v)[k]? = some v := by
  simp

end DownstreamBench.Verify
