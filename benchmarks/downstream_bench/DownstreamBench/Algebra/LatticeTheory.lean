import DownstreamBench.Prelude

namespace DownstreamBench.Algebra

structure OrderHom (α : Type u) (β : Type v) (leA : α → α → Prop) (leB : β → β → Prop) where
  toFun : α → β
  mono : ∀ a₁ a₂, leA a₁ a₂ → leB (toFun a₁) (toFun a₂)

def OrderHom.comp {leA : α → α → Prop} {leB : β → β → Prop} {leC : γ → γ → Prop}
    (g : OrderHom β γ leB leC) (f : OrderHom α β leA leB) : OrderHom α γ leA leC where
  toFun a := g.toFun (f.toFun a)
  mono _ _ h := g.mono _ _ (f.mono _ _ h)

def OrderHom.id (leA : α → α → Prop) : OrderHom α α leA leA where
  toFun x := x
  mono _ _ h := h

theorem OrderHom.comp_assoc {leA : α → α → Prop} {leB : β → β → Prop}
    {leC : γ → γ → Prop} {leD : δ → δ → Prop}
    (h : OrderHom γ δ leC leD) (g : OrderHom β γ leB leC) (f : OrderHom α β leA leB) :
    OrderHom.comp (OrderHom.comp h g) f = OrderHom.comp h (OrderHom.comp g f) := rfl

structure GaloisConn (α : Type u) (β : Type v) (leA : α → α → Prop) (leB : β → β → Prop) where
  lower : α → β
  upper : β → α
  adj : ∀ a b, leB (lower a) b ↔ leA a (upper b)

theorem GaloisConn.lower_mono {leA : α → α → Prop} {leB : β → β → Prop}
    (leA_trans : ∀ x y z, leA x y → leA y z → leA x z)
    (leB_refl : ∀ x, leB x x)
    (gc : GaloisConn α β leA leB) {a₁ a₂ : α} (h : leA a₁ a₂) :
    leB (gc.lower a₁) (gc.lower a₂) := by
  rw [gc.adj]
  exact leA_trans a₁ a₂ (gc.upper (gc.lower a₂)) h ((gc.adj a₂ (gc.lower a₂)).mp (leB_refl _))

theorem lattice_sup_idem [BenchLattice α] (a : α) :
    BenchLattice.sup a a = a := by
  apply BenchLattice.le_antisymm
  · exact BenchLattice.sup_le a a a (BenchLattice.le_refl a) (BenchLattice.le_refl a)
  · exact BenchLattice.le_sup_left a a

theorem lattice_inf_idem [BenchLattice α] (a : α) :
    BenchLattice.inf a a = a := by
  apply BenchLattice.le_antisymm
  · exact BenchLattice.inf_le_left a a
  · exact BenchLattice.le_inf a a a (BenchLattice.le_refl a) (BenchLattice.le_refl a)

theorem lattice_absorption [BenchLattice α] (a b : α) :
    BenchLattice.inf a (BenchLattice.sup a b) = a := by
  apply BenchLattice.le_antisymm
  · exact BenchLattice.inf_le_left a (BenchLattice.sup a b)
  · exact BenchLattice.le_inf a (BenchLattice.sup a b) a (BenchLattice.le_refl a) (BenchLattice.le_sup_left a b)

end DownstreamBench.Algebra
