import DownstreamBench.Algebra.MonoidLaws
import DownstreamBench.Algebra.LatticeTheory

namespace DownstreamBench.Verify

open DownstreamBench

/-- Deep polymorphic pipeline wrappers exercising repeated `isExprDefEq` across calls. -/
def pipe2 {α β γ : Type u} (f : α → β) (g : β → γ) (x : α) : γ := g (f x)
def pipe4 {α β γ δ ε : Type u} (f : α → β) (g : β → γ) (h : γ → δ) (k : δ → ε) (x : α) : ε :=
  k (h (g (f x)))

def foldBundle [BenchMonoid α] (a b c d : α) : α :=
  BenchMagma.mul (BenchMagma.mul a b) (BenchMagma.mul c d)

theorem pipe4_assoc {α β γ δ ε : Type u}
    (f : α → β) (g : β → γ) (h : γ → δ) (k : δ → ε) (x : α) :
    pipe4 f g h k x = pipe2 (pipe2 f g) (pipe2 h k) x := rfl

theorem foldBundle_reassoc [BenchMonoid α] (a b c d : α) :
    foldBundle a b c d = BenchMagma.mul a (BenchMagma.mul b (BenchMagma.mul c d)) := by
  simp only [foldBundle, BenchSemigroup.mul_assoc]

theorem foldBundle_comm [BenchCommMonoid α] (a b c d : α) :
    foldBundle a b c d = foldBundle d c b a := by
  simp only [foldBundle]
  calc BenchMagma.mul (BenchMagma.mul a b) (BenchMagma.mul c d)
      = BenchMagma.mul (BenchMagma.mul c d) (BenchMagma.mul a b) := BenchCommMonoid.mul_comm _ _
    _ = BenchMagma.mul (BenchMagma.mul d c) (BenchMagma.mul a b) := by rw [BenchCommMonoid.mul_comm c d]
    _ = BenchMagma.mul (BenchMagma.mul d c) (BenchMagma.mul b a) := by rw [BenchCommMonoid.mul_comm a b]

theorem defeq_mesh_01 (a b c d : Nat) :
    foldBundle a b c d = foldBundle d c b a := foldBundle_comm a b c d

theorem defeq_mesh_02 (a b c d : BitVec 32) :
    foldBundle a b c d = foldBundle d c b a := foldBundle_comm a b c d

theorem defeq_mesh_03 (a b c d : Nat × BitVec 32) :
    foldBundle a b c d = foldBundle d c b a := foldBundle_comm a b c d

theorem defeq_mesh_04 (a b c d : (Nat × Nat) × (BitVec 16 × BitVec 32)) :
    foldBundle a b c d = foldBundle d c b a := foldBundle_comm a b c d

theorem defeq_mesh_05 (a b c d : Nat × (BitVec 8 × (Nat × BitVec 16))) :
    foldBundle a b c d = foldBundle d c b a := foldBundle_comm a b c d

theorem defeq_mesh_06 (x y z w : Nat) :
    pipe4 (· + x) (· + y) (· + z) (· + w) 0 =
      pipe2 (pipe2 (· + x) (· + y)) (pipe2 (· + z) (· + w)) 0 := by
  exact pipe4_assoc _ _ _ _ 0

end DownstreamBench.Verify
