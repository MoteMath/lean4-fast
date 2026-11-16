import DownstreamBench.Prelude

namespace DownstreamBench.Logic

inductive Ty where
  | base : Nat → Ty
  | arrow : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  deriving Repr, DecidableEq, BEq

inductive LamTerm where
  | var : Nat → LamTerm
  | lam : Ty → LamTerm → LamTerm
  | app : LamTerm → LamTerm → LamTerm
  | pair : LamTerm → LamTerm → LamTerm
  | fst : LamTerm → LamTerm
  | snd : LamTerm → LamTerm
  deriving Repr, DecidableEq

def LamTerm.shift (d c : Nat) : LamTerm → LamTerm
  | .var k => if k < c then .var k else .var (k + d)
  | .lam ty body => .lam ty (body.shift d (c + 1))
  | .app f a => .app (f.shift d c) (a.shift d c)
  | .pair a b => .pair (a.shift d c) (b.shift d c)
  | .fst p => .fst (p.shift d c)
  | .snd p => .snd (p.shift d c)

def LamTerm.size : LamTerm → Nat
  | .var _ => 1
  | .lam _ b => 1 + b.size
  | .app f a => 1 + f.size + a.size
  | .pair a b => 1 + a.size + b.size
  | .fst p => 1 + p.size
  | .snd p => 1 + p.size

def LamTerm.subst (t : LamTerm) (j : Nat) (s : LamTerm) : LamTerm :=
  match t with
  | .var k => if k == j then s else .var k
  | .lam ty body => .lam ty (body.subst (j + 1) (s.shift 1 0))
  | .app f a => .app (f.subst j s) (a.subst j s)
  | .pair a b => .pair (a.subst j s) (b.subst j s)
  | .fst p => .fst (p.subst j s)
  | .snd p => .snd (p.subst j s)
termination_by t

@[simp] theorem LamTerm.shift_zero (t : LamTerm) (c : Nat) :
    t.shift 0 c = t := by
  induction t generalizing c <;> simp [LamTerm.shift, *]

theorem LamTerm.size_shift (t : LamTerm) (d c : Nat) :
    (t.shift d c).size = t.size := by
  induction t generalizing c with
  | var k => by_cases h : k < c <;> simp [LamTerm.shift, LamTerm.size, h]
  | lam _ _ ih => simp [LamTerm.shift, LamTerm.size, ih]
  | app _ _ ih1 ih2 => simp [LamTerm.shift, LamTerm.size, ih1, ih2]
  | pair _ _ ih1 ih2 => simp [LamTerm.shift, LamTerm.size, ih1, ih2]
  | fst _ ih => simp [LamTerm.shift, LamTerm.size, ih]
  | snd _ ih => simp [LamTerm.shift, LamTerm.size, ih]

inductive HasType : List Ty → LamTerm → Ty → Prop where
  | var : ∀ {Γ k τ}, Γ[k]? = some τ → HasType Γ (.var k) τ
  | lam : ∀ {Γ τ₁ τ₂ body}, HasType (τ₁ :: Γ) body τ₂ → HasType Γ (.lam τ₁ body) (.arrow τ₁ τ₂)
  | app : ∀ {Γ f a τ₁ τ₂}, HasType Γ f (.arrow τ₁ τ₂) → HasType Γ a τ₁ → HasType Γ (.app f a) τ₂
  | pair : ∀ {Γ a b τ₁ τ₂}, HasType Γ a τ₁ → HasType Γ b τ₂ → HasType Γ (.pair a b) (.prod τ₁ τ₂)
  | fst : ∀ {Γ p τ₁ τ₂}, HasType Γ p (.prod τ₁ τ₂) → HasType Γ (.fst p) τ₁
  | snd : ∀ {Γ p τ₁ τ₂}, HasType Γ p (.prod τ₁ τ₂) → HasType Γ (.snd p) τ₂

theorem hasType_identity (τ : Ty) :
    HasType [] (.lam τ (.var 0)) (.arrow τ τ) := by
  apply HasType.lam
  apply HasType.var
  rfl

theorem hasType_compose (α β γ : Ty) :
    HasType [] (.lam (.arrow β γ) (.lam (.arrow α β) (.lam α (.app (.var 2) (.app (.var 1) (.var 0))))))
      (.arrow (.arrow β γ) (.arrow (.arrow α β) (.arrow α γ))) := by
  apply HasType.lam
  apply HasType.lam
  apply HasType.lam
  apply HasType.app
  · exact HasType.var rfl
  · exact HasType.app (HasType.var rfl) (HasType.var rfl)

end DownstreamBench.Logic
