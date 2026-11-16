import Std

/-!
# DownstreamBench.Prelude

Shared umbrella module for the Downstream Formalization Benchmark Suite.
Imports full `Std` (and transitive `Init`) hierarchies and defines algebraic
typeclasses, symbolic ASTs, recursive evaluators, and canonical rewrite lemmas
consumed across all downstream layers.
-/

namespace DownstreamBench

class BenchMagma (α : Type u) where
  mul : α → α → α

class BenchSemigroup (α : Type u) extends BenchMagma α where
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)

class BenchMonoid (α : Type u) extends BenchSemigroup α where
  one : α
  one_mul : ∀ a : α, mul one a = a
  mul_one : ∀ a : α, mul a one = a

class BenchCommMonoid (α : Type u) extends BenchMonoid α where
  mul_comm : ∀ a b : α, mul a b = mul b a

class BenchSemiring (α : Type u) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  zero_add : ∀ a : α, add zero a = a
  add_zero : ∀ a : α, add a zero = a
  add_comm : ∀ a b : α, add a b = add b a
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : α, mul one a = a
  mul_one : ∀ a : α, mul a one = a
  zero_mul : ∀ a : α, mul zero a = zero
  mul_zero : ∀ a : α, mul a zero = zero
  left_distrib : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)

class BenchLattice (α : Type u) where
  le : α → α → Prop
  bot : α
  top : α
  sup : α → α → α
  inf : α → α → α
  le_refl : ∀ a : α, le a a
  le_trans : ∀ a b c : α, le a b → le b c → le a c
  le_antisymm : ∀ a b : α, le a b → le b a → a = b
  bot_le : ∀ a : α, le bot a
  le_top : ∀ a : α, le a top
  le_sup_left : ∀ a b : α, le a (sup a b)
  le_sup_right : ∀ a b : α, le b (sup a b)
  sup_le : ∀ a b c : α, le a c → le b c → le (sup a b) c
  inf_le_left : ∀ a b : α, le (inf a b) a
  inf_le_right : ∀ a b : α, le (inf a b) b
  le_inf : ∀ a b c : α, le c a → le c b → le c (inf a b)

instance : BenchCommMonoid Nat where
  mul := (· + ·)
  mul_assoc := Nat.add_assoc
  one := 0
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
  mul_comm := Nat.add_comm

instance : BenchSemiring Nat where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib

instance : BenchSemiring Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_comm := Int.add_comm
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

instance {w : Nat} : BenchCommMonoid (BitVec w) where
  mul := (· + ·)
  mul_assoc := BitVec.add_assoc
  one := 0#w
  one_mul := BitVec.zero_add
  mul_one := BitVec.add_zero
  mul_comm := BitVec.add_comm

instance [BenchMonoid α] [BenchMonoid β] : BenchMonoid (α × β) where
  mul p q := (BenchMagma.mul p.1 q.1, BenchMagma.mul p.2 q.2)
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp [BenchSemigroup.mul_assoc]
  one := (BenchMonoid.one, BenchMonoid.one)
  one_mul a := by
    cases a
    simp [BenchMonoid.one_mul]
  mul_one a := by
    cases a
    simp [BenchMonoid.mul_one]

instance [BenchCommMonoid α] [BenchCommMonoid β] : BenchCommMonoid (α × β) where
  mul_comm a b := by
    cases a; cases b
    change (BenchMagma.mul _ _, BenchMagma.mul _ _) = (BenchMagma.mul _ _, BenchMagma.mul _ _)
    rw [BenchCommMonoid.mul_comm (α := α), BenchCommMonoid.mul_comm (α := β)]

instance : BenchLattice Bool where
  le a b := (!a) || b
  bot := false
  top := true
  sup := (· || ·)
  inf := (· && ·)
  le_refl a := by cases a <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  bot_le a := by cases a <;> rfl
  le_top a := by cases a <;> rfl
  le_sup_left a b := by cases a <;> cases b <;> rfl
  le_sup_right a b := by cases a <;> cases b <;> rfl
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide
  inf_le_left a b := by cases a <;> cases b <;> rfl
  inf_le_right a b := by cases a <;> cases b <;> rfl
  le_inf a b c := by cases a <;> cases b <;> cases c <;> decide

/-- Polynomial-time iterative monoid power for WHNF and DefEq benchmarks. -/
def mpow [BenchMonoid α] (x : α) : Nat → α
  | 0 => BenchMonoid.one
  | n + 1 => BenchMagma.mul x (mpow x n)

@[simp, grind =] theorem mpow_zero [BenchMonoid α] (x : α) :
    mpow x 0 = BenchMonoid.one := rfl

@[simp, grind =] theorem mpow_succ [BenchMonoid α] (x : α) (n : Nat) :
    mpow x (n + 1) = BenchMagma.mul x (mpow x n) := rfl

/-- Deep recursive open-term reducer used across WHNF benchmarks. -/
def iterApply {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterApply f n (f x)

@[simp, grind =] theorem iterApply_zero {α : Type u} (f : α → α) (x : α) :
    iterApply f 0 x = x := rfl

@[simp, grind =] theorem iterApply_succ {α : Type u} (f : α → α) (n : Nat) (x : α) :
    iterApply f (n + 1) x = iterApply f n (f x) := rfl

theorem iterApply_add {α : Type u} (f : α → α) (m n : Nat) (x : α) :
    iterApply f (m + n) x = iterApply f n (iterApply f m x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, iterApply_succ, iterApply_succ, ih]

/-- Shared symbolic expression AST for simp/grind/evaluator benchmarks. -/
inductive SymExpr where
  | lit : Int → SymExpr
  | var : Nat → SymExpr
  | neg : SymExpr → SymExpr
  | add : SymExpr → SymExpr → SymExpr
  | mul : SymExpr → SymExpr → SymExpr
  deriving Repr, DecidableEq, BEq, Hashable

def SymExpr.eval (env : Nat → Int) : SymExpr → Int
  | .lit k => k
  | .var i => env i
  | .neg e => -e.eval env
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env

@[simp, grind =] theorem SymExpr.eval_lit (env : Nat → Int) (k : Int) :
    (SymExpr.lit k).eval env = k := rfl

@[simp, grind =] theorem SymExpr.eval_var (env : Nat → Int) (i : Nat) :
    (SymExpr.var i).eval env = env i := rfl

@[simp, grind =] theorem SymExpr.eval_neg (env : Nat → Int) (e : SymExpr) :
    (SymExpr.neg e).eval env = -e.eval env := rfl

@[simp, grind =] theorem SymExpr.eval_add (env : Nat → Int) (a b : SymExpr) :
    (SymExpr.add a b).eval env = a.eval env + b.eval env := rfl

@[simp, grind =] theorem SymExpr.eval_mul (env : Nat → Int) (a b : SymExpr) :
    (SymExpr.mul a b).eval env = a.eval env * b.eval env := rfl

def SymExpr.size : SymExpr → Nat
  | .lit _ => 1
  | .var _ => 1
  | .neg e => 1 + e.size
  | .add a b => 1 + a.size + b.size
  | .mul a b => 1 + a.size + b.size

theorem SymExpr.size_pos (e : SymExpr) : e.size ≥ 1 := by
  cases e <;> simp [SymExpr.size] <;> omega

end DownstreamBench
