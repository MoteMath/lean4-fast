import Std

/-!
# SyntheticBench.Base

Shared algebraic hierarchy, outParam actions, symbolic ASTs, binary trees,
and canonical rewrite lemmas used across S1–S6 and Fanout/Mod01..Mod64.
-/

namespace SyntheticBench

class SB_Magma (α : Type u) where
  op : α → α → α

class SB_Semigroup (α : Type u) extends SB_Magma α where
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c)

class SB_Monoid (α : Type u) extends SB_Semigroup α where
  unit : α
  unit_op : ∀ a : α, op unit a = a
  op_unit : ∀ a : α, op a unit = a

class SB_CommMonoid (α : Type u) extends SB_Monoid α where
  op_comm : ∀ a b : α, op a b = op b a

class SB_Semiring (α : Type u) where
  z : α
  u : α
  add : α → α → α
  mul : α → α → α
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  z_add : ∀ a : α, add z a = a
  add_z : ∀ a : α, add a z = a
  add_comm : ∀ a b : α, add a b = add b a
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  u_mul : ∀ a : α, mul u a = a
  mul_u : ∀ a : α, mul a u = a
  z_mul : ∀ a : α, mul z a = z
  mul_z : ∀ a : α, mul a z = z

class ScalarAct (R : Type u) (M : outParam (Type v)) where
  smul : R → M → M

class Normed (α : Type u) (N : outParam (Type v)) where
  norm : α → N

structure Tagged (tag : Nat) (α : Type u) where
  val : α
  deriving Repr, DecidableEq, Hashable

structure Vec2 (α : Type u) where
  x : α
  y : α
  deriving Repr, DecidableEq, Hashable

inductive ExprTree (α : Type u) where
  | leaf : α → ExprTree α
  | neg  : ExprTree α → ExprTree α
  | add  : ExprTree α → ExprTree α → ExprTree α
  | mul  : ExprTree α → ExprTree α → ExprTree α
  deriving Repr, DecidableEq

def ExprTree.size : ExprTree α → Nat
  | .leaf _ => 1
  | .neg a => a.size + 1
  | .add a b => a.size + b.size + 1
  | .mul a b => a.size + b.size + 1

def ExprTree.map (f : α → β) : ExprTree α → ExprTree β
  | .leaf x => .leaf (f x)
  | .neg a => .neg (a.map f)
  | .add a b => .add (a.map f) (b.map f)
  | .mul a b => .mul (a.map f) (b.map f)

def ExprTree.mirror : ExprTree α → ExprTree α
  | .leaf x => .leaf x
  | .neg a => .neg a.mirror
  | .add a b => .add b.mirror a.mirror
  | .mul a b => .mul b.mirror a.mirror

def ExprTree.evalInt : ExprTree Int → Int
  | .leaf k => k
  | .neg a => -a.evalInt
  | .add a b => a.evalInt + b.evalInt
  | .mul a b => a.evalInt * b.evalInt

@[simp, grind =] theorem ExprTree.size_map (f : α → β) (t : ExprTree α) :
    (t.map f).size = t.size := by
  induction t <;> simp [ExprTree.map, ExprTree.size, *]

@[simp, grind =] theorem ExprTree.size_mirror (t : ExprTree α) :
    t.mirror.size = t.size := by
  induction t <;> simp [ExprTree.mirror, ExprTree.size, *] <;> omega

@[simp, grind =] theorem ExprTree.mirror_mirror (t : ExprTree α) :
    t.mirror.mirror = t := by
  induction t <;> simp [ExprTree.mirror, *]

@[simp] theorem ExprTree.evalInt_mirror (t : ExprTree Int) :
    t.mirror.evalInt = t.evalInt := by
  induction t with
  | leaf _ => rfl
  | neg a ih => simp [ExprTree.mirror, ExprTree.evalInt, ih]
  | add a b iha ihb => simp [ExprTree.mirror, ExprTree.evalInt, iha, ihb, Int.add_comm]
  | mul a b iha ihb => simp [ExprTree.mirror, ExprTree.evalInt, iha, ihb, Int.mul_comm]

instance : SB_CommMonoid Nat where
  op := (· + ·)
  unit := 0
  op_assoc := Nat.add_assoc
  unit_op := Nat.zero_add
  op_unit := Nat.add_zero
  op_comm := Nat.add_comm

instance : SB_Semiring Nat where
  z := 0
  u := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := Nat.add_assoc
  z_add := Nat.zero_add
  add_z := Nat.add_zero
  add_comm := Nat.add_comm
  mul_assoc := Nat.mul_assoc
  u_mul := Nat.one_mul
  mul_u := Nat.mul_one
  z_mul := Nat.zero_mul
  mul_z := Nat.mul_zero

instance : Normed Nat Nat where
  norm n := n

instance : ScalarAct Nat Nat where
  smul a b := a * b

instance (tag : Nat) [SB_Magma α] : SB_Magma (Tagged tag α) where
  op a b := ⟨SB_Magma.op a.val b.val⟩

instance (tag : Nat) [SB_Semigroup α] : SB_Semigroup (Tagged tag α) where
  op_assoc a b c := by
    cases a; cases b; cases c
    simp [SB_Magma.op, SB_Semigroup.op_assoc]

instance (tag : Nat) [SB_Monoid α] : SB_Monoid (Tagged tag α) where
  unit := ⟨SB_Monoid.unit⟩
  unit_op a := by cases a; simp [SB_Magma.op, SB_Monoid.unit_op]
  op_unit a := by cases a; simp [SB_Magma.op, SB_Monoid.op_unit]

instance (tag : Nat) [SB_CommMonoid α] : SB_CommMonoid (Tagged tag α) where
  op_comm a b := by
    cases a; cases b
    change Tagged.mk (SB_Magma.op _ _) = Tagged.mk (SB_Magma.op _ _)
    rw [SB_CommMonoid.op_comm]

instance [Normed α N] (tag : Nat) : Normed (Tagged tag α) N where
  norm a := Normed.norm a.val

instance [SB_Semiring α] : SB_Semiring (Vec2 α) where
  z := ⟨SB_Semiring.z, SB_Semiring.z⟩
  u := ⟨SB_Semiring.u, SB_Semiring.u⟩
  add a b := ⟨SB_Semiring.add a.x b.x, SB_Semiring.add a.y b.y⟩
  mul a b := ⟨SB_Semiring.mul a.x b.x, SB_Semiring.mul a.y b.y⟩
  add_assoc a b c := by
    cases a; cases b; cases c
    simp [SB_Semiring.add_assoc]
  z_add a := by cases a; simp [SB_Semiring.z_add]
  add_z a := by cases a; simp [SB_Semiring.add_z]
  add_comm a b := by
    cases a; cases b
    change Vec2.mk _ _ = Vec2.mk _ _
    congr 1 <;> exact SB_Semiring.add_comm _ _
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp [SB_Semiring.mul_assoc]
  u_mul a := by cases a; simp [SB_Semiring.u_mul]
  mul_u a := by cases a; simp [SB_Semiring.mul_u]
  z_mul a := by cases a; simp [SB_Semiring.z_mul]
  mul_z a := by cases a; simp [SB_Semiring.mul_z]

def sbPow [SB_Monoid α] (x : α) : Nat → α
  | 0 => SB_Monoid.unit
  | n + 1 => SB_Magma.op x (sbPow x n)

end SyntheticBench
