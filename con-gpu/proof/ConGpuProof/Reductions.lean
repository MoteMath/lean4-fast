/-
ConGpuProof.Reductions
======================
Formal Lean 4 soundness proofs for:
1. Weak-head parallel reduction, Church-Rosser confluence, `Quot.lift` / `Quot.ind`
   (`KIND_QUOT`), and `Eq.rec` / indexed `iota` reduction soundness (`quotLift_sound`,
   `quotInd_sound`, `eqRec_iota_sound`, `indexedIota_sound`).
2. Compositional verification of frozen persistent environment prefixes under
   incremental declaration appends (`verifiedPrefix_append_sound`).
-/

import ConGpuProof.ArenaSpec
import ConGpuProof.ArenaOps

namespace ConGpuProof

/-! ### 1. Kernel Syntax for `Quot`, `Eq`, and Higher-Order Reduction -/

/-- Extended kernel AST modeling lambda-calculus plus primitive `Quot` and `Eq`
    recursor nodes corresponding to `con-gpu` `KIND_QUOT` / indexed `iota` rules. -/
inductive QExpr where
  | bvar (idx : Nat)
  | fvar (id : Nat)
  | sort (lvl : Nat)
  | const (cid : Nat)
  | app (fn arg : QExpr)
  | lam (dom body : QExpr)
  | forallE (dom cod : QExpr)
  | quotTy (α r : QExpr)
  | quotMk (α r a : QExpr)
  | quotLift (α r β f h q : QExpr)
  | quotInd (α r β h q : QExpr)
  | eqTy (α a b : QExpr)
  | eqRefl (α a : QExpr)
  | eqRec (α a motive minor b e : QExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Environment mapping constant IDs to optional closed unfolding bodies. -/
abbrev QEnv := Array (Option QExpr)

/-- Bound-variable closure at cutoff `k`: every `bvar idx` has `idx < k`. -/
def QClosed (k : Nat) : QExpr -> Prop
  | .bvar idx => idx < k
  | .fvar _ | .sort _ | .const _ => True
  | .app fn arg => QClosed k fn ∧ QClosed k arg
  | .lam dom body => QClosed k dom ∧ QClosed (k + 1) body
  | .forallE dom cod => QClosed k dom ∧ QClosed (k + 1) cod
  | .quotTy α r => QClosed k α ∧ QClosed k r
  | .quotMk α r a => QClosed k α ∧ QClosed k r ∧ QClosed k a
  | .quotLift α r β f h q =>
    QClosed k α ∧ QClosed k r ∧ QClosed k β ∧ QClosed k f ∧ QClosed k h ∧ QClosed k q
  | .quotInd α r β h q =>
    QClosed k α ∧ QClosed k r ∧ QClosed k β ∧ QClosed k h ∧ QClosed k q
  | .eqTy α a b => QClosed k α ∧ QClosed k a ∧ QClosed k b
  | .eqRefl α a => QClosed k α ∧ QClosed k a
  | .eqRec α a m minor b e =>
    QClosed k α ∧ QClosed k a ∧ QClosed k m ∧ QClosed k minor ∧ QClosed k b ∧ QClosed k e

/-- Every unfolding body in `QEnv` is closed (`QClosed 0`). -/
abbrev QEnvClosed (env : QEnv) : Prop :=
  ∀ (cid : Nat) (v : QExpr), env[cid]? = some (some v) -> QClosed 0 v

/-- Shift bound indices `≥ c` upward by `d`. -/
def QExpr.shift (c d : Nat) : QExpr -> QExpr
  | .bvar i => if i < c then .bvar i else .bvar (i + d)
  | .fvar id => .fvar id
  | .sort lvl => .sort lvl
  | .const cid => .const cid
  | .app fn arg => .app (fn.shift c d) (arg.shift c d)
  | .lam dom body => .lam (dom.shift c d) (body.shift (c + 1) d)
  | .forallE dom cod => .forallE (dom.shift c d) (cod.shift (c + 1) d)
  | .quotTy α r => .quotTy (α.shift c d) (r.shift c d)
  | .quotMk α r a => .quotMk (α.shift c d) (r.shift c d) (a.shift c d)
  | .quotLift α r β f h q =>
    .quotLift (α.shift c d) (r.shift c d) (β.shift c d) (f.shift c d) (h.shift c d) (q.shift c d)
  | .quotInd α r β h q =>
    .quotInd (α.shift c d) (r.shift c d) (β.shift c d) (h.shift c d) (q.shift c d)
  | .eqTy α a b => .eqTy (α.shift c d) (a.shift c d) (b.shift c d)
  | .eqRefl α a => .eqRefl (α.shift c d) (a.shift c d)
  | .eqRec α a m minor b e =>
    .eqRec (α.shift c d) (a.shift c d) (m.shift c d) (minor.shift c d) (b.shift c d) (e.shift c d)

/-- Capture-avoiding de Bruijn substitution at binder depth `k`. -/
def QExpr.subst (e : QExpr) (k : Nat) (s : QExpr) : QExpr :=
  match e with
  | .bvar i =>
    if i == k then s.shift 0 k
    else if k < i then .bvar (i - 1)
    else .bvar i
  | .fvar id => .fvar id
  | .sort lvl => .sort lvl
  | .const cid => .const cid
  | .app fn arg => .app (fn.subst k s) (arg.subst k s)
  | .lam dom body => .lam (dom.subst k s) (body.subst (k + 1) s)
  | .forallE dom cod => .forallE (dom.subst k s) (cod.subst (k + 1) s)
  | .quotTy α r => .quotTy (α.subst k s) (r.subst k s)
  | .quotMk α r a => .quotMk (α.subst k s) (r.subst k s) (a.subst k s)
  | .quotLift α r β f h q =>
    .quotLift (α.subst k s) (r.subst k s) (β.subst k s) (f.subst k s) (h.subst k s) (q.subst k s)
  | .quotInd α r β h q =>
    .quotInd (α.subst k s) (r.subst k s) (β.subst k s) (h.subst k s) (q.subst k s)
  | .eqTy α a b => .eqTy (α.subst k s) (a.subst k s) (b.subst k s)
  | .eqRefl α a => .eqRefl (α.subst k s) (a.subst k s)
  | .eqRec α a m minor b e =>
    .eqRec (α.subst k s) (a.subst k s) (m.subst k s) (minor.subst k s) (b.subst k s) (e.subst k s)

theorem qClosed_shift_eq : ∀ {k : Nat} {e : QExpr}, QClosed k e ->
    ∀ {c d}, k ≤ c -> e.shift c d = e
  | k, .bvar i, h, c, d, hc => by
    simp only [QClosed] at h
    have hi : i < c := Nat.lt_of_lt_of_le h hc
    simp [QExpr.shift, hi]
  | _, .fvar _, _, _, _, _ => rfl
  | _, .sort _, _, _, _, _ => rfl
  | _, .const _, _, _, _, _ => rfl
  | k, .app f a, h, c, d, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2 hc]
  | k, .lam d b, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc,
      qClosed_shift_eq h.2 (Nat.succ_le_succ hc)]
  | k, .forallE d b, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc,
      qClosed_shift_eq h.2 (Nat.succ_le_succ hc)]
  | k, .quotTy α r, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2 hc]
  | k, .quotMk α r a, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2.1 hc,
      qClosed_shift_eq h.2.2 hc]
  | k, .quotLift α r β f prf q, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2.1 hc,
      qClosed_shift_eq h.2.2.1 hc, qClosed_shift_eq h.2.2.2.1 hc,
      qClosed_shift_eq h.2.2.2.2.1 hc, qClosed_shift_eq h.2.2.2.2.2 hc]
  | k, .quotInd α r β prf q, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2.1 hc,
      qClosed_shift_eq h.2.2.1 hc, qClosed_shift_eq h.2.2.2.1 hc,
      qClosed_shift_eq h.2.2.2.2 hc]
  | k, .eqTy α a b, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2.1 hc,
      qClosed_shift_eq h.2.2 hc]
  | k, .eqRefl α a, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2 hc]
  | k, .eqRec α a m minor b e, h, c, sh, hc => by
    simp only [QClosed] at h
    simp only [QExpr.shift, qClosed_shift_eq h.1 hc, qClosed_shift_eq h.2.1 hc,
      qClosed_shift_eq h.2.2.1 hc, qClosed_shift_eq h.2.2.2.1 hc,
      qClosed_shift_eq h.2.2.2.2.1 hc, qClosed_shift_eq h.2.2.2.2.2 hc]

theorem qClosed_subst_eq : ∀ {m : Nat} {e : QExpr}, QClosed m e ->
    ∀ {k s}, m ≤ k -> e.subst k s = e
  | m, .bvar i, h, k, s, hk => by
    simp only [QClosed] at h
    have hlt : i < k := Nat.lt_of_lt_of_le h hk
    have hne : (i == k) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
    have hnl : ¬ k < i := Nat.not_lt.mpr (Nat.le_of_lt hlt)
    simp [QExpr.subst, hne, hnl]
  | _, .fvar _, _, _, _, _ => rfl
  | _, .sort _, _, _, _, _ => rfl
  | _, .const _, _, _, _, _ => rfl
  | m, .app f a, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2 hk]
  | m, .lam d b, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk,
      qClosed_subst_eq h.2 (Nat.succ_le_succ hk)]
  | m, .forallE d b, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk,
      qClosed_subst_eq h.2 (Nat.succ_le_succ hk)]
  | m, .quotTy α r, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2 hk]
  | m, .quotMk α r a, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2.1 hk,
      qClosed_subst_eq h.2.2 hk]
  | m, .quotLift α r β f prf q, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2.1 hk,
      qClosed_subst_eq h.2.2.1 hk, qClosed_subst_eq h.2.2.2.1 hk,
      qClosed_subst_eq h.2.2.2.2.1 hk, qClosed_subst_eq h.2.2.2.2.2 hk]
  | m, .quotInd α r β prf q, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2.1 hk,
      qClosed_subst_eq h.2.2.1 hk, qClosed_subst_eq h.2.2.2.1 hk,
      qClosed_subst_eq h.2.2.2.2 hk]
  | m, .eqTy α a b, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2.1 hk,
      qClosed_subst_eq h.2.2 hk]
  | m, .eqRefl α a, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2 hk]
  | m, .eqRec α a mt minor b e, h, k, s, hk => by
    simp only [QClosed] at h
    simp only [QExpr.subst, qClosed_subst_eq h.1 hk, qClosed_subst_eq h.2.1 hk,
      qClosed_subst_eq h.2.2.1 hk, qClosed_subst_eq h.2.2.2.1 hk,
      qClosed_subst_eq h.2.2.2.2.1 hk, qClosed_subst_eq h.2.2.2.2.2 hk]

theorem QExpr.shift_zero (e : QExpr) : ∀ c, e.shift c 0 = e := by
  induction e with
  | bvar i => intro c; unfold QExpr.shift; split <;> simp
  | fvar _ | sort _ | const _ => intro _; rfl
  | app fn arg ih1 ih2 => intro c; simp [QExpr.shift, ih1 c, ih2 c]
  | lam dom body ih1 ih2 => intro c; simp [QExpr.shift, ih1 c, ih2 (c + 1)]
  | forallE dom cod ih1 ih2 => intro c; simp [QExpr.shift, ih1 c, ih2 (c + 1)]
  | quotTy α r ih1 ih2 => intro c; simp [QExpr.shift, ih1 c, ih2 c]
  | quotMk α r a ih1 ih2 ih3 => intro c; simp [QExpr.shift, ih1 c, ih2 c, ih3 c]
  | quotLift α r β f h q ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c; simp [QExpr.shift, ih1 c, ih2 c, ih3 c, ih4 c, ih5 c, ih6 c]
  | quotInd α r β h q ih1 ih2 ih3 ih4 ih5 =>
    intro c; simp [QExpr.shift, ih1 c, ih2 c, ih3 c, ih4 c, ih5 c]
  | eqTy α a b ih1 ih2 ih3 => intro c; simp [QExpr.shift, ih1 c, ih2 c, ih3 c]
  | eqRefl α a ih1 ih2 => intro c; simp [QExpr.shift, ih1 c, ih2 c]
  | eqRec α a m minor b e ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c; simp [QExpr.shift, ih1 c, ih2 c, ih3 c, ih4 c, ih5 c, ih6 c]

theorem QExpr.shift_shift_add (e : QExpr) :
    ∀ c₁ c₂ d₁ d₂, c₁ ≤ c₂ -> c₂ ≤ c₁ + d₁ ->
      (e.shift c₁ d₁).shift c₂ d₂ = e.shift c₁ (d₁ + d₂) := by
  induction e with
  | bvar i =>
    intro c₁ c₂ d₁ d₂ h1 h2
    by_cases hlt1 : i < c₁
    · have hlt2 : i < c₂ := Nat.lt_of_lt_of_le hlt1 h1
      simp only [QExpr.shift, hlt1, hlt2, ↓reduceIte]
    · have hge2 : ¬ (i + d₁ < c₂) := by omega
      simp only [QExpr.shift, hlt1, hge2, ↓reduceIte, Nat.add_assoc]
  | fvar _ | sort _ | const _ => intro _ _ _ _ _ _; rfl
  | app fn arg ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2]
  | lam dom body ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2,
      ih2 (c₁ + 1) (c₂ + 1) d₁ d₂ (by omega) (by omega)]
  | forallE dom cod ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2,
      ih2 (c₁ + 1) (c₂ + 1) d₁ d₂ (by omega) (by omega)]
  | quotTy α r ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2]
  | quotMk α r a ih1 ih2 ih3 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2, ih3 c₁ c₂ d₁ d₂ h1 h2]
  | quotLift α r β f h q ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2, ih3 c₁ c₂ d₁ d₂ h1 h2,
      ih4 c₁ c₂ d₁ d₂ h1 h2, ih5 c₁ c₂ d₁ d₂ h1 h2, ih6 c₁ c₂ d₁ d₂ h1 h2]
  | quotInd α r β h q ih1 ih2 ih3 ih4 ih5 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2, ih3 c₁ c₂ d₁ d₂ h1 h2,
      ih4 c₁ c₂ d₁ d₂ h1 h2, ih5 c₁ c₂ d₁ d₂ h1 h2]
  | eqTy α a b ih1 ih2 ih3 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2, ih3 c₁ c₂ d₁ d₂ h1 h2]
  | eqRefl α a ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2]
  | eqRec α a m minor b e ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c₁ c₂ d₁ d₂ h1 h2
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ h1 h2, ih2 c₁ c₂ d₁ d₂ h1 h2, ih3 c₁ c₂ d₁ d₂ h1 h2,
      ih4 c₁ c₂ d₁ d₂ h1 h2, ih5 c₁ c₂ d₁ d₂ h1 h2, ih6 c₁ c₂ d₁ d₂ h1 h2]

theorem QExpr.shift_shift_comm (e : QExpr) :
    ∀ c₁ c₂ d₁ d₂, c₁ ≤ c₂ ->
      (e.shift c₁ d₁).shift (c₂ + d₁) d₂ = (e.shift c₂ d₂).shift c₁ d₁ := by
  induction e with
  | bvar i =>
    intro c₁ c₂ d₁ d₂ hle
    by_cases h1 : i < c₁
    · have h2 : i < c₂ := by omega
      have h3 : i < c₂ + d₁ := by omega
      simp only [QExpr.shift, h1, h2, h3, ↓reduceIte]
    · by_cases h2 : i < c₂
      · have h3 : i + d₁ < c₂ + d₁ := by omega
        simp only [QExpr.shift, h1, h2, h3, ↓reduceIte]
      · have h3 : ¬ (i + d₁ < c₂ + d₁) := by omega
        have h4 : ¬ (i + d₂ < c₁) := by omega
        simp only [QExpr.shift, h1, h2, h3, h4, ↓reduceIte, Nat.add_right_comm]
  | fvar _ | sort _ | const _ => intro _ _ _ _ _; rfl
  | app fn arg ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle]
  | lam dom body ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ hle
    have hbody := ih2 (c₁ + 1) (c₂ + 1) d₁ d₂ (by omega)
    have heq : c₂ + 1 + d₁ = c₂ + d₁ + 1 := by omega
    rw [heq] at hbody
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, hbody]
  | forallE dom cod ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ hle
    have hcod := ih2 (c₁ + 1) (c₂ + 1) d₁ d₂ (by omega)
    have heq : c₂ + 1 + d₁ = c₂ + d₁ + 1 := by omega
    rw [heq] at hcod
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, hcod]
  | quotTy α r ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle]
  | quotMk α r a ih1 ih2 ih3 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle, ih3 c₁ c₂ d₁ d₂ hle]
  | quotLift α r β f h q ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle, ih3 c₁ c₂ d₁ d₂ hle,
      ih4 c₁ c₂ d₁ d₂ hle, ih5 c₁ c₂ d₁ d₂ hle, ih6 c₁ c₂ d₁ d₂ hle]
  | quotInd α r β h q ih1 ih2 ih3 ih4 ih5 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle, ih3 c₁ c₂ d₁ d₂ hle,
      ih4 c₁ c₂ d₁ d₂ hle, ih5 c₁ c₂ d₁ d₂ hle]
  | eqTy α a b ih1 ih2 ih3 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle, ih3 c₁ c₂ d₁ d₂ hle]
  | eqRefl α a ih1 ih2 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle]
  | eqRec α a m minor b e ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c₁ c₂ d₁ d₂ hle
    simp [QExpr.shift, ih1 c₁ c₂ d₁ d₂ hle, ih2 c₁ c₂ d₁ d₂ hle, ih3 c₁ c₂ d₁ d₂ hle,
      ih4 c₁ c₂ d₁ d₂ hle, ih5 c₁ c₂ d₁ d₂ hle, ih6 c₁ c₂ d₁ d₂ hle]

theorem QExpr.shift_subst_above (e a : QExpr) :
    ∀ c k d, (e.subst k a).shift (c + k) d = (e.shift (c + k + 1) d).subst k (a.shift c d) := by
  induction e with
  | bvar i =>
    intro c k d
    by_cases hik : i = k
    · subst hik
      have hlt : i < c + i + 1 := by omega
      simp only [QExpr.subst, beq_self_eq_true, ↓reduceIte, QExpr.shift, hlt]
      exact QExpr.shift_shift_comm a 0 c i d (Nat.zero_le c)
    · have hbeq : (i == k) = false := beq_false_of_ne hik
      by_cases hki : k < i
      · by_cases hc : i - 1 < c + k
        · have hc1 : i < c + k + 1 := by omega
          simp only [QExpr.subst, hbeq, Bool.false_eq_true, ↓reduceIte, hki, QExpr.shift, hc, hc1]
        · have hc1 : ¬ (i < c + k + 1) := by omega
          have hki' : k < i + d := by omega
          have hne' : (i + d == k) = false := beq_false_of_ne (by omega)
          simp only [QExpr.subst, hbeq, Bool.false_eq_true, ↓reduceIte, hki, QExpr.shift, hc, hc1, hne', hki']
          congr 1; omega
      · have hlt : i < c + k := by omega
        have hlt1 : i < c + k + 1 := by omega
        simp only [QExpr.subst, hbeq, Bool.false_eq_true, ↓reduceIte, hki, QExpr.shift, hlt, hlt1]
  | fvar _ | sort _ | const _ => intro _ _ _; rfl
  | app fn arg ih1 ih2 =>
    intro c k d
    simp only [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d]
  | lam dom body ih1 ih2 =>
    intro c k d
    have hbody := ih2 c (k + 1) d
    have heq1 : c + (k + 1) = c + k + 1 := by omega
    rw [heq1] at hbody
    simp only [QExpr.subst, QExpr.shift, ih1 c k d, hbody]
  | forallE dom cod ih1 ih2 =>
    intro c k d
    have hcod := ih2 c (k + 1) d
    have heq1 : c + (k + 1) = c + k + 1 := by omega
    rw [heq1] at hcod
    simp only [QExpr.subst, QExpr.shift, ih1 c k d, hcod]
  | quotTy α r ih1 ih2 =>
    intro c k d
    simp [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d]
  | quotMk α r a' ih1 ih2 ih3 =>
    intro c k d
    simp [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d, ih3 c k d]
  | quotLift α r β f h q ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c k d
    simp [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d, ih3 c k d, ih4 c k d, ih5 c k d, ih6 c k d]
  | quotInd α r β h q ih1 ih2 ih3 ih4 ih5 =>
    intro c k d
    simp [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d, ih3 c k d, ih4 c k d, ih5 c k d]
  | eqTy α a' b ih1 ih2 ih3 =>
    intro c k d
    simp [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d, ih3 c k d]
  | eqRefl α a' ih1 ih2 =>
    intro c k d
    simp [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d]
  | eqRec α a' m minor b e ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c k d
    simp [QExpr.subst, QExpr.shift, ih1 c k d, ih2 c k d, ih3 c k d, ih4 c k d, ih5 c k d, ih6 c k d]

theorem QExpr.shift_subst_zero (e a : QExpr) (c d : Nat) :
    (e.subst 0 a).shift c d = (e.shift (c + 1) d).subst 0 (a.shift c d) := by
  simpa using QExpr.shift_subst_above e a c 0 d

theorem QExpr.subst_shift_cancel (s u : QExpr) :
    ∀ c n d, n ≤ d -> (s.shift c (d + 1)).subst (c + n) u = s.shift c d := by
  induction s with
  | bvar i =>
    intro c n d hle
    unfold QExpr.shift QExpr.subst
    by_cases hi : i < c
    · have hne : (i == c + n) = false := beq_false_of_ne (by omega)
      have hnl : ¬ c + n < i := by omega
      simp [hi, hne, hnl]
    · have hgt : c + n < i + (d + 1) := by omega
      have hne : (i + (d + 1) == c + n) = false := beq_false_of_ne (by omega)
      simp [hi, hgt, hne]
  | fvar _ | sort _ | const _ => intro _ _ _ _; rfl
  | app fn arg ih1 ih2 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle]
  | lam dom body ih1 ih2 =>
    intro c n d hle
    have hb := ih2 (c + 1) n d hle
    have heq : c + 1 + n = c + n + 1 := by omega
    rw [heq] at hb
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, hb]
  | forallE dom cod ih1 ih2 =>
    intro c n d hle
    have hc := ih2 (c + 1) n d hle
    have heq : c + 1 + n = c + n + 1 := by omega
    rw [heq] at hc
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, hc]
  | quotTy α r ih1 ih2 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle]
  | quotMk α r a ih1 ih2 ih3 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle, ih3 c n d hle]
  | quotLift α r β f h q ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle, ih3 c n d hle,
      ih4 c n d hle, ih5 c n d hle, ih6 c n d hle]
  | quotInd α r β h q ih1 ih2 ih3 ih4 ih5 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle, ih3 c n d hle,
      ih4 c n d hle, ih5 c n d hle]
  | eqTy α a b ih1 ih2 ih3 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle, ih3 c n d hle]
  | eqRefl α a ih1 ih2 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle]
  | eqRec α a m minor b e ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c n d hle
    simp [QExpr.shift, QExpr.subst, ih1 c n d hle, ih2 c n d hle, ih3 c n d hle,
      ih4 c n d hle, ih5 c n d hle, ih6 c n d hle]

theorem QExpr.shift_subst_below (e s : QExpr) :
    ∀ c k m, m ≤ k -> (e.shift c m).subst (c + k) s = (e.subst (c + (k - m)) s).shift c m := by
  induction e with
  | bvar i =>
    intro c k m hle
    by_cases hci : i < c
    · have h1 : (i == c + k) = false := beq_false_of_ne (by omega)
      have h2 : ¬ c + k < i := by omega
      have h3 : (i == c + (k - m)) = false := beq_false_of_ne (by omega)
      have h4 : ¬ c + (k - m) < i := by omega
      simp only [QExpr.shift, hci, ↓reduceIte, QExpr.subst, h1, h2, h3, h4, Bool.false_eq_true]
    · by_cases heq : i = c + (k - m)
      · subst heq
        have h1 : (c + (k - m) + m == c + k) = true := beq_iff_eq.mpr (by omega)
        simp only [QExpr.shift, hci, ↓reduceIte, QExpr.subst, h1, beq_self_eq_true]
        have hadd := QExpr.shift_shift_add s 0 c (c + (k - m)) m (Nat.zero_le c) (by omega)
        rw [hadd]
        congr 1; omega
      · by_cases hlt : i < c + (k - m)
        · have h1 : (i + m == c + k) = false := beq_false_of_ne (by omega)
          have h2 : ¬ c + k < i + m := by omega
          have h3 : (i == c + (k - m)) = false := beq_false_of_ne heq
          have h4 : ¬ c + (k - m) < i := by omega
          simp only [QExpr.shift, hci, ↓reduceIte, QExpr.subst, h1, h2, h3, h4, Bool.false_eq_true]
        · have hgt : c + (k - m) < i := by omega
          have hgt' : c + k < i + m := by omega
          have h1 : (i + m == c + k) = false := beq_false_of_ne (by omega)
          have h3 : (i == c + (k - m)) = false := beq_false_of_ne heq
          have hc' : ¬ (i - 1 < c) := by omega
          simp only [QExpr.shift, hci, ↓reduceIte, QExpr.subst, h1, hgt', h3, hgt, hc', Bool.false_eq_true]
          congr 1; omega
  | fvar _ | sort _ | const _ => intro _ _ _ _; rfl
  | app fn arg ih1 ih2 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle]
  | lam dom body ih1 ih2 =>
    intro c k m hle
    have hb := ih2 (c + 1) k m hle
    have heq1 : c + 1 + k = c + k + 1 := by omega
    have heq2 : c + 1 + (k - m) = c + (k - m) + 1 := by omega
    rw [heq1, heq2] at hb
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, hb]
  | forallE dom cod ih1 ih2 =>
    intro c k m hle
    have hc := ih2 (c + 1) k m hle
    have heq1 : c + 1 + k = c + k + 1 := by omega
    have heq2 : c + 1 + (k - m) = c + (k - m) + 1 := by omega
    rw [heq1, heq2] at hc
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, hc]
  | quotTy α r ih1 ih2 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle]
  | quotMk α r a ih1 ih2 ih3 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle, ih3 c k m hle]
  | quotLift α r β f h q ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle, ih3 c k m hle,
      ih4 c k m hle, ih5 c k m hle, ih6 c k m hle]
  | quotInd α r β h q ih1 ih2 ih3 ih4 ih5 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle, ih3 c k m hle,
      ih4 c k m hle, ih5 c k m hle]
  | eqTy α a b ih1 ih2 ih3 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle, ih3 c k m hle]
  | eqRefl α a ih1 ih2 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle]
  | eqRec α a m' minor b e ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c k m hle
    simp [QExpr.shift, QExpr.subst, ih1 c k m hle, ih2 c k m hle, ih3 c k m hle,
      ih4 c k m hle, ih5 c k m hle, ih6 c k m hle]

theorem QExpr.subst_subst (e a s : QExpr) :
    ∀ m k, m ≤ k ->
      (e.subst m a).subst k s = (e.subst (k + 1) s).subst m (a.subst (k - m) s) := by
  induction e with
  | bvar i =>
    intro m k hmk
    by_cases him : i = m
    · subst him
      have h1 : (i == k + 1) = false := beq_false_of_ne (by omega)
      have h2 : ¬ k + 1 < i := by omega
      simp only [QExpr.subst, beq_self_eq_true, ↓reduceIte, h1, h2, Bool.false_eq_true]
      simpa [Nat.zero_add] using QExpr.shift_subst_below a s 0 k i hmk
    · by_cases hik : i = k + 1
      · subst hik
        have h1 : (k + 1 == m) = false := beq_false_of_ne (by omega)
        have h2 : m < k + 1 := by omega
        have h3 : (k + 1 - 1 == k) = true := beq_iff_eq.mpr (by omega)
        simp only [QExpr.subst, h1, h2, h3, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        simpa [Nat.zero_add] using (QExpr.subst_shift_cancel s (a.subst (k - m) s) 0 m k hmk).symm
      · have hbm : (i == m) = false := beq_false_of_ne him
        have hbk : (i == k + 1) = false := beq_false_of_ne hik
        by_cases hltm : i < m
        · have h1 : ¬ m < i := by omega
          have h2 : ¬ k + 1 < i := by omega
          have h3 : (i == k) = false := beq_false_of_ne (by omega)
          have h4 : ¬ k < i := by omega
          simp only [QExpr.subst, hbm, hbk, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
        · by_cases hgtk : k + 1 < i
          · have h1 : m < i := by omega
            have h2 : k < i - 1 := by omega
            have h3 : (i - 1 == k) = false := beq_false_of_ne (by omega)
            have h4 : (i - 1 == m) = false := beq_false_of_ne (by omega)
            have h5 : m < i - 1 := by omega
            simp only [QExpr.subst, hbm, hbk, h1, hgtk, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]
          · have h1 : m < i := by omega
            have h2 : ¬ k + 1 < i := by omega
            have h3 : ¬ k < i - 1 := by omega
            have h4 : (i - 1 == k) = false := beq_false_of_ne (by omega)
            simp only [QExpr.subst, hbm, hbk, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
  | fvar _ | sort _ | const _ => intro _ _ _; rfl
  | app fn arg ih1 ih2 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk]
  | lam dom body ih1 ih2 =>
    intro m k hmk
    have hb := ih2 (m + 1) (k + 1) (by omega)
    have heq : k + 1 - (m + 1) = k - m := by omega
    rw [heq] at hb
    simp [QExpr.subst, ih1 m k hmk, hb]
  | forallE dom cod ih1 ih2 =>
    intro m k hmk
    have hc := ih2 (m + 1) (k + 1) (by omega)
    have heq : k + 1 - (m + 1) = k - m := by omega
    rw [heq] at hc
    simp [QExpr.subst, ih1 m k hmk, hc]
  | quotTy α r ih1 ih2 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk]
  | quotMk α r a' ih1 ih2 ih3 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk, ih3 m k hmk]
  | quotLift α r β f h q ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk, ih3 m k hmk, ih4 m k hmk, ih5 m k hmk, ih6 m k hmk]
  | quotInd α r β h q ih1 ih2 ih3 ih4 ih5 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk, ih3 m k hmk, ih4 m k hmk, ih5 m k hmk]
  | eqTy α a' b ih1 ih2 ih3 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk, ih3 m k hmk]
  | eqRefl α a' ih1 ih2 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk]
  | eqRec α a' mt minor b e ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro m k hmk
    simp [QExpr.subst, ih1 m k hmk, ih2 m k hmk, ih3 m k hmk, ih4 m k hmk, ih5 m k hmk, ih6 m k hmk]

/-! ### 2. Parallel Reduction, Takahashi Complete Development, & Confluence -/

/-- One-step parallel reduction covering delta, beta, `Quot.lift`, `Quot.ind`, and `Eq.rec` iota. -/
inductive QParRed (env : QEnv) : QExpr -> QExpr -> Prop
  | bvar {i} : QParRed env (.bvar i) (.bvar i)
  | fvar {id} : QParRed env (.fvar id) (.fvar id)
  | sort {l} : QParRed env (.sort l) (.sort l)
  | const {cid} : QParRed env (.const cid) (.const cid)
  | delta {cid v} : env[cid]? = some (some v) -> QParRed env (.const cid) v
  | app {f f' a a'} : QParRed env f f' -> QParRed env a a' -> QParRed env (.app f a) (.app f' a')
  | beta {d b b' a a'} :
      QParRed env b b' -> QParRed env a a' ->
      QParRed env (.app (.lam d b) a) (b'.subst 0 a')
  | lam {d d' b b'} : QParRed env d d' -> QParRed env b b' -> QParRed env (.lam d b) (.lam d' b')
  | forallE {d d' c c'} :
      QParRed env d d' -> QParRed env c c' -> QParRed env (.forallE d c) (.forallE d' c')
  | quotTy {α α' r r'} :
      QParRed env α α' -> QParRed env r r' -> QParRed env (.quotTy α r) (.quotTy α' r')
  | quotMk {α α' r r' a a'} :
      QParRed env α α' -> QParRed env r r' -> QParRed env a a' ->
      QParRed env (.quotMk α r a) (.quotMk α' r' a')
  | quotLift {α α' r r' β β' f f' h h' q q'} :
      QParRed env α α' -> QParRed env r r' -> QParRed env β β' ->
      QParRed env f f' -> QParRed env h h' -> QParRed env q q' ->
      QParRed env (.quotLift α r β f h q) (.quotLift α' r' β' f' h' q')
  | quotLiftRed {α r β f f' h α' r' a a'} :
      QParRed env f f' -> QParRed env a a' ->
      QParRed env (.quotLift α r β f h (.quotMk α' r' a)) (.app f' a')
  | quotInd {α α' r r' β β' h h' q q'} :
      QParRed env α α' -> QParRed env r r' -> QParRed env β β' ->
      QParRed env h h' -> QParRed env q q' ->
      QParRed env (.quotInd α r β h q) (.quotInd α' r' β' h' q')
  | quotIndRed {α r β h h' α' r' a a'} :
      QParRed env h h' -> QParRed env a a' ->
      QParRed env (.quotInd α r β h (.quotMk α' r' a)) (.app h' a')
  | eqTy {α α' a a' b b'} :
      QParRed env α α' -> QParRed env a a' -> QParRed env b b' ->
      QParRed env (.eqTy α a b) (.eqTy α' a' b')
  | eqRefl {α α' a a'} :
      QParRed env α α' -> QParRed env a a' ->
      QParRed env (.eqRefl α a) (.eqRefl α' a')
  | eqRec {α α' a a' m m' minor minor' b b' e e'} :
      QParRed env α α' -> QParRed env a a' -> QParRed env m m' ->
      QParRed env minor minor' -> QParRed env b b' -> QParRed env e e' ->
      QParRed env (.eqRec α a m minor b e) (.eqRec α' a' m' minor' b' e')
  | eqRecRed {α a m minor minor' b α' a'} :
      QParRed env minor minor' ->
      QParRed env (.eqRec α a m minor b (.eqRefl α' a')) minor'

theorem qParRed_refl (env : QEnv) : ∀ e, QParRed env e e
  | .bvar _ => .bvar
  | .fvar _ => .fvar
  | .sort _ => .sort
  | .const _ => .const
  | .app f a => .app (qParRed_refl env f) (qParRed_refl env a)
  | .lam d b => .lam (qParRed_refl env d) (qParRed_refl env b)
  | .forallE d c => .forallE (qParRed_refl env d) (qParRed_refl env c)
  | .quotTy α r => .quotTy (qParRed_refl env α) (qParRed_refl env r)
  | .quotMk α r a => .quotMk (qParRed_refl env α) (qParRed_refl env r) (qParRed_refl env a)
  | .quotLift α r β f h q =>
    .quotLift (qParRed_refl env α) (qParRed_refl env r) (qParRed_refl env β)
      (qParRed_refl env f) (qParRed_refl env h) (qParRed_refl env q)
  | .quotInd α r β h q =>
    .quotInd (qParRed_refl env α) (qParRed_refl env r) (qParRed_refl env β)
      (qParRed_refl env h) (qParRed_refl env q)
  | .eqTy α a b => .eqTy (qParRed_refl env α) (qParRed_refl env a) (qParRed_refl env b)
  | .eqRefl α a => .eqRefl (qParRed_refl env α) (qParRed_refl env a)
  | .eqRec α a m minor b e =>
    .eqRec (qParRed_refl env α) (qParRed_refl env a) (qParRed_refl env m)
      (qParRed_refl env minor) (qParRed_refl env b) (qParRed_refl env e)

theorem qParRed_shift {env : QEnv} (henv : QEnvClosed env)
    {e e' : QExpr} (hr : QParRed env e e') :
    ∀ c d, QParRed env (e.shift c d) (e'.shift c d) := by
  induction hr with
  | bvar => intro c d; unfold QExpr.shift; split <;> exact .bvar
  | fvar => intro _ _; exact .fvar
  | sort => intro _ _; exact .sort
  | const => intro _ _; exact .const
  | @delta cid v hlu =>
    intro c d
    have hc0 := henv cid v hlu
    rw [qClosed_shift_eq hc0 (Nat.zero_le c)]
    exact .delta hlu
  | app _ _ ih1 ih2 => intro c d; exact .app (ih1 c d) (ih2 c d)
  | @beta d b b' a a' _ _ ih1 ih2 =>
    intro c sh
    simp only [QExpr.shift]
    rw [QExpr.shift_subst_zero b' a' c sh]
    exact .beta (ih1 (c + 1) sh) (ih2 c sh)
  | lam _ _ ih1 ih2 => intro c d; exact .lam (ih1 c d) (ih2 (c + 1) d)
  | forallE _ _ ih1 ih2 => intro c d; exact .forallE (ih1 c d) (ih2 (c + 1) d)
  | quotTy _ _ ih1 ih2 => intro c d; exact .quotTy (ih1 c d) (ih2 c d)
  | quotMk _ _ _ ih1 ih2 ih3 => intro c d; exact .quotMk (ih1 c d) (ih2 c d) (ih3 c d)
  | quotLift _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c d; exact .quotLift (ih1 c d) (ih2 c d) (ih3 c d) (ih4 c d) (ih5 c d) (ih6 c d)
  | quotLiftRed _ _ ih1 ih2 => intro c d; exact .quotLiftRed (ih1 c d) (ih2 c d)
  | quotInd _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    intro c d; exact .quotInd (ih1 c d) (ih2 c d) (ih3 c d) (ih4 c d) (ih5 c d)
  | quotIndRed _ _ ih1 ih2 => intro c d; exact .quotIndRed (ih1 c d) (ih2 c d)
  | eqTy _ _ _ ih1 ih2 ih3 => intro c d; exact .eqTy (ih1 c d) (ih2 c d) (ih3 c d)
  | eqRefl _ _ ih1 ih2 => intro c d; exact .eqRefl (ih1 c d) (ih2 c d)
  | eqRec _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro c d; exact .eqRec (ih1 c d) (ih2 c d) (ih3 c d) (ih4 c d) (ih5 c d) (ih6 c d)
  | eqRecRed _ ih1 => intro c d; exact .eqRecRed (ih1 c d)

theorem qParRed_subst {env : QEnv} (henv : QEnvClosed env)
    {e e' : QExpr} (hr : QParRed env e e') :
    ∀ {s s' : QExpr}, QParRed env s s' -> ∀ (k : Nat),
      QParRed env (e.subst k s) (e'.subst k s') := by
  induction hr with
  | @bvar i =>
    intro s s' hs k
    by_cases hik : i = k
    · subst hik
      simp only [QExpr.subst, beq_self_eq_true, ↓reduceIte]
      exact qParRed_shift henv hs 0 i
    · have hne : (i == k) = false := beq_false_of_ne hik
      by_cases hki : k < i
      · simp only [QExpr.subst, hne, Bool.false_eq_true, ↓reduceIte, hki]; exact .bvar
      · simp only [QExpr.subst, hne, Bool.false_eq_true, ↓reduceIte, hki]; exact .bvar
  | fvar => intro _ _ _ _; exact .fvar
  | sort => intro _ _ _ _; exact .sort
  | const => intro _ _ _ _; exact .const
  | @delta cid v hlu =>
    intro s s' _ k
    have hc0 := henv cid v hlu
    rw [qClosed_subst_eq hc0 (Nat.zero_le k)]
    exact .delta hlu
  | app _ _ ih1 ih2 => intro s s' hs k; exact .app (ih1 hs k) (ih2 hs k)
  | @beta d b b' a a' _ _ ih1 ih2 =>
    intro s s' hs k
    simp only [QExpr.subst]
    rw [QExpr.subst_subst b' a' s' 0 k (Nat.zero_le k), Nat.sub_zero]
    exact .beta (ih1 hs (k + 1)) (ih2 hs k)
  | lam _ _ ih1 ih2 => intro s s' hs k; exact .lam (ih1 hs k) (ih2 hs (k + 1))
  | forallE _ _ ih1 ih2 => intro s s' hs k; exact .forallE (ih1 hs k) (ih2 hs (k + 1))
  | quotTy _ _ ih1 ih2 => intro s s' hs k; exact .quotTy (ih1 hs k) (ih2 hs k)
  | quotMk _ _ _ ih1 ih2 ih3 => intro s s' hs k; exact .quotMk (ih1 hs k) (ih2 hs k) (ih3 hs k)
  | quotLift _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro s s' hs k
    exact .quotLift (ih1 hs k) (ih2 hs k) (ih3 hs k) (ih4 hs k) (ih5 hs k) (ih6 hs k)
  | quotLiftRed _ _ ih1 ih2 => intro s s' hs k; exact .quotLiftRed (ih1 hs k) (ih2 hs k)
  | quotInd _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    intro s s' hs k
    exact .quotInd (ih1 hs k) (ih2 hs k) (ih3 hs k) (ih4 hs k) (ih5 hs k)
  | quotIndRed _ _ ih1 ih2 => intro s s' hs k; exact .quotIndRed (ih1 hs k) (ih2 hs k)
  | eqTy _ _ _ ih1 ih2 ih3 => intro s s' hs k; exact .eqTy (ih1 hs k) (ih2 hs k) (ih3 hs k)
  | eqRefl _ _ ih1 ih2 => intro s s' hs k; exact .eqRefl (ih1 hs k) (ih2 hs k)
  | eqRec _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    intro s s' hs k
    exact .eqRec (ih1 hs k) (ih2 hs k) (ih3 hs k) (ih4 hs k) (ih5 hs k) (ih6 hs k)
  | eqRecRed _ ih1 => intro s s' hs k; exact .eqRecRed (ih1 hs k)

/-- Takahashi's complete parallel development for `QParRed`. -/
def qDev (env : QEnv) : QExpr -> QExpr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .sort l => .sort l
  | .const cid =>
    match env[cid]? with
    | some (some v) => v
    | _ => .const cid
  | .app (.lam _ body) arg => (qDev env body).subst 0 (qDev env arg)
  | .app fn arg => .app (qDev env fn) (qDev env arg)
  | .lam d b => .lam (qDev env d) (qDev env b)
  | .forallE d c => .forallE (qDev env d) (qDev env c)
  | .quotTy α r => .quotTy (qDev env α) (qDev env r)
  | .quotMk α r a => .quotMk (qDev env α) (qDev env r) (qDev env a)
  | .quotLift _ _ _ f _ (.quotMk _ _ a) => .app (qDev env f) (qDev env a)
  | .quotLift α r β f h q =>
    .quotLift (qDev env α) (qDev env r) (qDev env β) (qDev env f) (qDev env h) (qDev env q)
  | .quotInd _ _ _ h (.quotMk _ _ a) => .app (qDev env h) (qDev env a)
  | .quotInd α r β h q =>
    .quotInd (qDev env α) (qDev env r) (qDev env β) (qDev env h) (qDev env q)
  | .eqTy α a b => .eqTy (qDev env α) (qDev env a) (qDev env b)
  | .eqRefl α a => .eqRefl (qDev env α) (qDev env a)
  | .eqRec _ _ _ minor _ (.eqRefl _ _) => qDev env minor
  | .eqRec α a m minor b e =>
    .eqRec (qDev env α) (qDev env a) (qDev env m) (qDev env minor) (qDev env b) (qDev env e)

theorem qParRed_to_dev {env : QEnv} (henv : QEnvClosed env)
    {a b : QExpr} (h : QParRed env a b) :
    QParRed env b (qDev env a) := by
  induction h with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | sort => exact .sort
  | @const cid =>
    unfold qDev
    cases hlu : env[cid]? with
    | none => exact .const
    | some mv =>
      cases mv with
      | none => exact .const
      | some v => exact .delta hlu
  | @delta cid v hlu =>
    unfold qDev
    rw [hlu]
    exact qParRed_refl env v
  | @app f f' a a' hf ha ihf iha =>
    cases f with
    | lam d body =>
      cases hf with
      | @lam _ d' _ b' hd hb =>
        unfold qDev at ihf ⊢
        cases ihf with
        | lam _ ihb => exact .beta ihb iha
    | bvar _ | fvar _ | sort _ | const _ | app _ _ | forallE _ _
    | quotTy _ _ | quotMk _ _ _ | quotLift _ _ _ _ _ _ | quotInd _ _ _ _ _
    | eqTy _ _ _ | eqRefl _ _ | eqRec _ _ _ _ _ _ =>
      exact .app ihf iha
  | @beta d b b' a a' hb ha ihb iha =>
    exact qParRed_subst henv ihb iha 0
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | quotTy _ _ ih1 ih2 => exact .quotTy ih1 ih2
  | quotMk _ _ _ ih1 ih2 ih3 => exact .quotMk ih1 ih2 ih3
  | @quotLift α α' r r' β β' f f' h h' q q' hα hr hβ hf hh hq ihα ihr ihβ ihf ihh ihq =>
    cases q with
    | quotMk α0 r0 a0 =>
      cases hq with
      | quotMk _ _ ha0 =>
        cases ihq with
        | quotMk _ _ iha0 => exact .quotLiftRed ihf iha0
    | bvar _ | fvar _ | sort _ | const _ | app _ _ | lam _ _ | forallE _ _
    | quotTy _ _ | quotLift _ _ _ _ _ _ | quotInd _ _ _ _ _
    | eqTy _ _ _ | eqRefl _ _ | eqRec _ _ _ _ _ _ =>
      exact .quotLift ihα ihr ihβ ihf ihh ihq
  | quotLiftRed _ _ ihf iha => exact .app ihf iha
  | @quotInd α α' r r' β β' h h' q q' hα hr hβ hh hq ihα ihr ihβ ihh ihq =>
    cases q with
    | quotMk α0 r0 a0 =>
      cases hq with
      | quotMk _ _ ha0 =>
        cases ihq with
        | quotMk _ _ iha0 => exact .quotIndRed ihh iha0
    | bvar _ | fvar _ | sort _ | const _ | app _ _ | lam _ _ | forallE _ _
    | quotTy _ _ | quotLift _ _ _ _ _ _ | quotInd _ _ _ _ _
    | eqTy _ _ _ | eqRefl _ _ | eqRec _ _ _ _ _ _ =>
      exact .quotInd ihα ihr ihβ ihh ihq
  | quotIndRed _ _ ihh iha => exact .app ihh iha
  | eqTy _ _ _ ih1 ih2 ih3 => exact .eqTy ih1 ih2 ih3
  | eqRefl _ _ ih1 ih2 => exact .eqRefl ih1 ih2
  | @eqRec α α' a a' m m' minor minor' b b' e e' hα ha hm hminor hb he
      ihα iha ihm ihminor ihb ihe =>
    cases e with
    | eqRefl α0 a0 =>
      cases he with
      | eqRefl => exact .eqRecRed ihminor
    | bvar _ | fvar _ | sort _ | const _ | app _ _ | lam _ _ | forallE _ _
    | quotTy _ _ | quotMk _ _ _ | quotLift _ _ _ _ _ _ | quotInd _ _ _ _ _
    | eqTy _ _ _ | eqRec _ _ _ _ _ _ =>
      exact .eqRec ihα iha ihm ihminor ihb ihe
  | eqRecRed _ ihminor => exact ihminor

theorem qParRed_diamond {env : QEnv} (henv : QEnvClosed env) {a b c : QExpr}
    (h1 : QParRed env a b) (h2 : QParRed env a c) :
    ∃ d, QParRed env b d ∧ QParRed env c d :=
  ⟨qDev env a, qParRed_to_dev henv h1, qParRed_to_dev henv h2⟩

/-- Multi-step parallel reduction (`ReflTransGen`). -/
inductive QParRedStar (env : QEnv) : QExpr -> QExpr -> Prop
  | refl (a : QExpr) : QParRedStar env a a
  | step {a b c : QExpr} : QParRed env a b -> QParRedStar env b c -> QParRedStar env a c

theorem QParRedStar.single {env : QEnv} {a b : QExpr} (h : QParRed env a b) :
    QParRedStar env a b :=
  .step h (.refl b)

theorem QParRedStar.trans {env : QEnv} {a b c : QExpr}
    (h1 : QParRedStar env a b) (h2 : QParRedStar env b c) : QParRedStar env a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

theorem qParRedStar_strip {env : QEnv} (henv : QEnvClosed env) {a b c : QExpr}
    (hstar : QParRedStar env a b) (hstep : QParRed env a c) :
    ∃ d, QParRedStar env b d ∧ QParRedStar env c d := by
  induction hstar generalizing c with
  | refl => exact ⟨c, .single hstep, .refl c⟩
  | @step x y z hxy hyz ih =>
    obtain ⟨w, hyw, hcw⟩ := qParRed_diamond henv hxy hstep
    obtain ⟨d, hzd, hwd⟩ := ih hyw
    exact ⟨d, hzd, .step hcw hwd⟩

theorem qParRedStar_confluent {env : QEnv} (henv : QEnvClosed env) {a b c : QExpr}
    (h1 : QParRedStar env a b) (h2 : QParRedStar env a c) :
    ∃ d, QParRedStar env b d ∧ QParRedStar env c d := by
  induction h1 generalizing c with
  | refl => exact ⟨c, h2, .refl c⟩
  | @step x y z hxy hyz ih =>
    obtain ⟨w, hcw, hyw⟩ := qParRedStar_strip henv h2 hxy
    obtain ⟨d, hzd, hwd⟩ := ih hyw
    exact ⟨d, hzd, QParRedStar.trans hcw hwd⟩

/-- Definitional equality: common multi-step parallel reduct (Church-Rosser joinability). -/
def QDefEq (env : QEnv) (a b : QExpr) : Prop :=
  ∃ z, QParRedStar env a z ∧ QParRedStar env b z

theorem qDefEq_refl (env : QEnv) (a : QExpr) : QDefEq env a a :=
  ⟨a, .refl a, .refl a⟩

theorem qDefEq_symm {env : QEnv} {a b : QExpr} (h : QDefEq env a b) : QDefEq env b a :=
  ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩

theorem qDefEq_trans {env : QEnv} (henv : QEnvClosed env) {a b c : QExpr}
    (h1 : QDefEq env a b) (h2 : QDefEq env b c) : QDefEq env a c := by
  rcases h1 with ⟨z1, haz1, hbz1⟩
  rcases h2 with ⟨z2, hbz2, hcz2⟩
  obtain ⟨z, hz1, hz2⟩ := qParRedStar_confluent henv hbz1 hbz2
  exact ⟨z, haz1.trans hz1, hcz2.trans hz2⟩

theorem qDefEq_of_parRed {env : QEnv} {a b : QExpr} (h : QParRed env a b) : QDefEq env a b :=
  ⟨b, .single h, .refl b⟩

theorem qDefEq_app {env : QEnv} (_henv : QEnvClosed env) {f₁ f₂ a₁ a₂ : QExpr}
    (hf : QDefEq env f₁ f₂) (ha : QDefEq env a₁ a₂) :
    QDefEq env (.app f₁ a₁) (.app f₂ a₂) := by
  rcases hf with ⟨fz, hf1, hf2⟩
  rcases ha with ⟨az, ha1, ha2⟩
  have liftL : ∀ {x y arg}, QParRedStar env x y -> QParRedStar env (.app x arg) (.app y arg) := by
    intro x y arg hxy
    induction hxy with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.app hs (qParRed_refl env arg)) ih
  have liftR : ∀ {fn x y}, QParRedStar env x y -> QParRedStar env (.app fn x) (.app fn y) := by
    intro fn x y hxy
    induction hxy with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.app (qParRed_refl env fn) hs) ih
  exact ⟨.app fz az, (liftL hf1).trans (liftR ha1), (liftL hf2).trans (liftR ha2)⟩

theorem qDefEq_eqRefl {env : QEnv} {α₁ α₂ a₁ a₂ : QExpr}
    (hα : QDefEq env α₁ α₂) (ha : QDefEq env a₁ a₂) :
    QDefEq env (.eqRefl α₁ a₁) (.eqRefl α₂ a₂) := by
  rcases hα with ⟨αz, hα1, hα2⟩
  rcases ha with ⟨az, ha1, ha2⟩
  have liftL : ∀ {x y a}, QParRedStar env x y -> QParRedStar env (.eqRefl x a) (.eqRefl y a) := by
    intro x y a hxy
    induction hxy with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.eqRefl hs (qParRed_refl env a)) ih
  have liftR : ∀ {α x y}, QParRedStar env x y -> QParRedStar env (.eqRefl α x) (.eqRefl α y) := by
    intro α x y hxy
    induction hxy with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.eqRefl (qParRed_refl env α) hs) ih
  exact ⟨.eqRefl αz az, (liftL hα1).trans (liftR ha1), (liftL hα2).trans (liftR ha2)⟩

theorem qDefEq_quotMk {env : QEnv} {α₁ α₂ r₁ r₂ a₁ a₂ : QExpr}
    (hα : QDefEq env α₁ α₂) (hr : QDefEq env r₁ r₂) (ha : QDefEq env a₁ a₂) :
    QDefEq env (.quotMk α₁ r₁ a₁) (.quotMk α₂ r₂ a₂) := by
  rcases hα with ⟨αz, hα1, hα2⟩
  rcases hr with ⟨rz, hr1, hr2⟩
  rcases ha with ⟨az, ha1, ha2⟩
  have lift1 : ∀ {x y r a}, QParRedStar env x y ->
      QParRedStar env (.quotMk x r a) (.quotMk y r a) := by
    intro x y r a hxy
    induction hxy with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.quotMk hs (qParRed_refl env r) (qParRed_refl env a)) ih
  have lift2 : ∀ {α x y a}, QParRedStar env x y ->
      QParRedStar env (.quotMk α x a) (.quotMk α y a) := by
    intro α x y a hxy
    induction hxy with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.quotMk (qParRed_refl env α) hs (qParRed_refl env a)) ih
  have lift3 : ∀ {α r x y}, QParRedStar env x y ->
      QParRedStar env (.quotMk α r x) (.quotMk α r y) := by
    intro α r x y hxy
    induction hxy with
    | refl => exact .refl _
    | step hs _ ih => exact .step (.quotMk (qParRed_refl env α) (qParRed_refl env r) hs) ih
  exact ⟨.quotMk αz rz az, ((lift1 hα1).trans (lift2 hr1)).trans (lift3 ha1),
    ((lift1 hα2).trans (lift2 hr2)).trans (lift3 ha2)⟩

/-! ### 3. Canonical Constructor Injectivity from Confluence -/

private theorem qParRedStar_quotTy_shape {env : QEnv} :
    ∀ {α r z : QExpr}, QParRedStar env (.quotTy α r) z ->
      ∃ α' r', z = .quotTy α' r' ∧ QParRedStar env α α' ∧ QParRedStar env r r' := by
  suffices h : ∀ {x z}, QParRedStar env x z ->
      ∀ α r, x = .quotTy α r ->
        ∃ α' r', z = .quotTy α' r' ∧ QParRedStar env α α' ∧ QParRedStar env r r' by
    intro α r z hst; exact h hst α r rfl
  intro x z hst
  induction hst with
  | refl =>
    intro α r hx; subst hx
    exact ⟨α, r, rfl, .refl α, .refl r⟩
  | @step x y z hxy hyz ih =>
    intro α r hx; subst hx
    cases hxy with
    | quotTy hα hr =>
      obtain ⟨α'', r'', hzeq, hαs, hrs⟩ := ih _ _ rfl
      exact ⟨α'', r'', hzeq, .step hα hαs, .step hr hrs⟩

theorem qDefEq_quotTy_inj {env : QEnv} {α₁ α₂ r₁ r₂ : QExpr}
    (h : QDefEq env (.quotTy α₁ r₁) (.quotTy α₂ r₂)) :
    QDefEq env α₁ α₂ ∧ QDefEq env r₁ r₂ := by
  rcases h with ⟨z, h1, h2⟩
  obtain ⟨α1', r1', hz1, hα1, hr1⟩ := qParRedStar_quotTy_shape h1
  obtain ⟨α2', r2', hz2, hα2, hr2⟩ := qParRedStar_quotTy_shape h2
  rw [hz1] at hz2
  injection hz2 with hαeq hreq
  rw [← hαeq] at hα2
  rw [← hreq] at hr2
  exact ⟨⟨α1', hα1, hα2⟩, ⟨r1', hr1, hr2⟩⟩

private theorem qParRedStar_eqTy_shape {env : QEnv} :
    ∀ {α a b z : QExpr}, QParRedStar env (.eqTy α a b) z ->
      ∃ α' a' b', z = .eqTy α' a' b' ∧
        QParRedStar env α α' ∧ QParRedStar env a a' ∧ QParRedStar env b b' := by
  suffices h : ∀ {x z}, QParRedStar env x z ->
      ∀ α a b, x = .eqTy α a b ->
        ∃ α' a' b', z = .eqTy α' a' b' ∧
          QParRedStar env α α' ∧ QParRedStar env a a' ∧ QParRedStar env b b' by
    intro α a b z hst; exact h hst α a b rfl
  intro x z hst
  induction hst with
  | refl =>
    intro α a b hx; subst hx
    exact ⟨α, a, b, rfl, .refl α, .refl a, .refl b⟩
  | @step x y z hxy hyz ih =>
    intro α a b hx; subst hx
    cases hxy with
    | eqTy hα ha hb =>
      obtain ⟨α'', a'', b'', hzeq, hαs, has, hbs⟩ := ih _ _ _ rfl
      exact ⟨α'', a'', b'', hzeq, .step hα hαs, .step ha has, .step hb hbs⟩

theorem qDefEq_eqTy_inj {env : QEnv} {α₁ α₂ a₁ a₂ b₁ b₂ : QExpr}
    (h : QDefEq env (.eqTy α₁ a₁ b₁) (.eqTy α₂ a₂ b₂)) :
    QDefEq env α₁ α₂ ∧ QDefEq env a₁ a₂ ∧ QDefEq env b₁ b₂ := by
  rcases h with ⟨z, h1, h2⟩
  obtain ⟨α1', a1', b1', hz1, hα1, ha1, hb1⟩ := qParRedStar_eqTy_shape h1
  obtain ⟨α2', a2', b2', hz2, hα2, ha2, hb2⟩ := qParRedStar_eqTy_shape h2
  rw [hz1] at hz2
  injection hz2 with hαeq haeq hbeq
  rw [← hαeq] at hα2
  rw [← haeq] at ha2
  rw [← hbeq] at hb2
  exact ⟨⟨α1', hα1, hα2⟩, ⟨a1', ha1, ha2⟩, ⟨b1', hb1, hb2⟩⟩

/-! ### 4. Dependent Kernel Typing & Soundness of `Quot` and `Eq.rec` / `iota` -/

/-- Declarative dependent typing judgment supporting `Quot`, `Eq`, and `QDefEq` conversion. -/
inductive QHasType (env : QEnv) : List QExpr -> QExpr -> QExpr -> Prop
  | bvar {ctx idx ty} :
      ctx[idx]? = some ty -> QHasType env ctx (.bvar idx) (ty.shift 0 (idx + 1))
  | sort {ctx lvl} : QHasType env ctx (.sort lvl) (.sort (lvl + 1))
  | app {ctx f a α β} :
      QHasType env ctx f (.forallE α β) ->
      QHasType env ctx a α ->
      QHasType env ctx (.app f a) (β.subst 0 a)
  | lam {ctx dom body u bodyTy} :
      QHasType env ctx dom (.sort u) ->
      QHasType env (dom :: ctx) body bodyTy ->
      QHasType env ctx (.lam dom body) (.forallE dom bodyTy)
  | forallE {ctx dom cod u v} :
      QHasType env ctx dom (.sort u) ->
      QHasType env (dom :: ctx) cod (.sort v) ->
      QHasType env ctx (.forallE dom cod) (.sort (imax u v))
  | quotTy {ctx α r u} :
      QHasType env ctx α (.sort u) ->
      QHasType env ctx r (.forallE α (.forallE (α.shift 0 1) (.sort 0))) ->
      QHasType env ctx (.quotTy α r) (.sort u)
  | quotMk {ctx α r a u} :
      QHasType env ctx α (.sort u) ->
      QHasType env ctx r (.forallE α (.forallE (α.shift 0 1) (.sort 0))) ->
      QHasType env ctx a α ->
      QHasType env ctx (.quotMk α r a) (.quotTy α r)
  | quotLift {ctx α r β f h q u v} :
      QHasType env ctx α (.sort u) ->
      QHasType env ctx r (.forallE α (.forallE (α.shift 0 1) (.sort 0))) ->
      QHasType env ctx β (.sort v) ->
      QHasType env ctx f (.forallE α (β.shift 0 1)) ->
      QHasType env ctx h
        (.forallE α (.forallE (α.shift 0 1)
          (.forallE (.app (.app (r.shift 0 2) (.bvar 1)) (.bvar 0))
            (.eqTy (β.shift 0 3) (.app (f.shift 0 3) (.bvar 2)) (.app (f.shift 0 3) (.bvar 1)))))) ->
      QHasType env ctx q (.quotTy α r) ->
      QHasType env ctx (.quotLift α r β f h q) β
  | quotInd {ctx α r β h q u} :
      QHasType env ctx α (.sort u) ->
      QHasType env ctx r (.forallE α (.forallE (α.shift 0 1) (.sort 0))) ->
      QHasType env ctx β (.forallE (.quotTy α r) (.sort 0)) ->
      QHasType env ctx h
        (.forallE α (.app (β.shift 0 1) (.quotMk (α.shift 0 1) (r.shift 0 1) (.bvar 0)))) ->
      QHasType env ctx q (.quotTy α r) ->
      QHasType env ctx (.quotInd α r β h q) (.app β q)
  | eqTy {ctx α a b u} :
      QHasType env ctx α (.sort u) ->
      QHasType env ctx a α ->
      QHasType env ctx b α ->
      QHasType env ctx (.eqTy α a b) (.sort 0)
  | eqRefl {ctx α a u} :
      QHasType env ctx α (.sort u) ->
      QHasType env ctx a α ->
      QHasType env ctx (.eqRefl α a) (.eqTy α a a)
  | eqRec {ctx α a motive minor b e u v} :
      QHasType env ctx α (.sort v) ->
      QHasType env ctx a α ->
      QHasType env ctx motive
        (.forallE α (.forallE (.eqTy (α.shift 0 1) (a.shift 0 1) (.bvar 0)) (.sort u))) ->
      QHasType env ctx minor (.app (.app motive a) (.eqRefl α a)) ->
      QHasType env ctx b α ->
      QHasType env ctx e (.eqTy α a b) ->
      QHasType env ctx (.eqRec α a motive minor b e) (.app (.app motive b) e)
  | conv {ctx e t₁ t₂ u} :
      QHasType env ctx e t₁ ->
      QDefEq env t₁ t₂ ->
      QHasType env ctx t₂ (.sort u) ->
      QHasType env ctx e t₂

private theorem qHasType_quotMk_inv {env : QEnv} (henv : QEnvClosed env) :
    ∀ {ctx α r a T}, QHasType env ctx (.quotMk α r a) T ->
      QHasType env ctx a α ∧ QDefEq env (.quotTy α r) T := by
  suffices h : ∀ {ctx e T}, QHasType env ctx e T ->
      ∀ α r a, e = .quotMk α r a ->
        QHasType env ctx a α ∧ QDefEq env (.quotTy α r) T by
    intro ctx α r a T hty; exact h hty α r a rfl
  intro ctx e T hty
  induction hty with
  | quotMk _ _ ha =>
    intro α r a heq; injection heq with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨ha, qDefEq_refl env _⟩
  | conv _ hde _ ih _ =>
    intro α r a heq
    obtain ⟨ha, hdt⟩ := ih α r a heq
    exact ⟨ha, qDefEq_trans henv hdt hde⟩
  | bvar | sort | app | lam | forallE | quotTy | quotLift | quotInd | eqTy | eqRefl | eqRec =>
    intro _ _ _ heq; cases heq

private theorem qHasType_quotLift_inv {env : QEnv} (henv : QEnvClosed env) :
    ∀ {ctx α r β f h q T}, QHasType env ctx (.quotLift α r β f h q) T ->
      QHasType env ctx f (.forallE α (β.shift 0 1)) ∧
      QHasType env ctx q (.quotTy α r) ∧
      QDefEq env β T := by
  suffices hs : ∀ {ctx e T}, QHasType env ctx e T ->
      ∀ α r β f h q, e = .quotLift α r β f h q ->
        QHasType env ctx f (.forallE α (β.shift 0 1)) ∧
        QHasType env ctx q (.quotTy α r) ∧
        QDefEq env β T by
    intro ctx α r β f h q T hty; exact hs hty α r β f h q rfl
  intro ctx e T hty
  induction hty with
  | quotLift _ _ _ hf _ hq =>
    intro α r β f h q heq; injection heq with h1 h2 h3 h4 h5 h6
    subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
    exact ⟨hf, hq, qDefEq_refl env _⟩
  | conv _ hde _ ih _ =>
    intro α r β f h q heq
    obtain ⟨hf, hq, hdt⟩ := ih α r β f h q heq
    exact ⟨hf, hq, qDefEq_trans henv hdt hde⟩
  | bvar | sort | app | lam | forallE | quotTy | quotMk | quotInd | eqTy | eqRefl | eqRec =>
    intro _ _ _ _ _ _ heq; cases heq

private theorem qHasType_quotInd_inv {env : QEnv} (henv : QEnvClosed env) :
    ∀ {ctx α r β h q T}, QHasType env ctx (.quotInd α r β h q) T ->
      QHasType env ctx h
        (.forallE α (.app (β.shift 0 1) (.quotMk (α.shift 0 1) (r.shift 0 1) (.bvar 0)))) ∧
      QHasType env ctx q (.quotTy α r) ∧
      QDefEq env (.app β q) T := by
  suffices hs : ∀ {ctx e T}, QHasType env ctx e T ->
      ∀ α r β h q, e = .quotInd α r β h q ->
        QHasType env ctx h
          (.forallE α (.app (β.shift 0 1) (.quotMk (α.shift 0 1) (r.shift 0 1) (.bvar 0)))) ∧
        QHasType env ctx q (.quotTy α r) ∧
        QDefEq env (.app β q) T by
    intro ctx α r β h q T hty; exact hs hty α r β h q rfl
  intro ctx e T hty
  induction hty with
  | quotInd _ _ _ hh hq =>
    intro α r β h q heq; injection heq with h1 h2 h3 h4 h5
    subst h1; subst h2; subst h3; subst h4; subst h5
    exact ⟨hh, hq, qDefEq_refl env _⟩
  | conv _ hde _ ih _ =>
    intro α r β h q heq
    obtain ⟨hh, hq, hdt⟩ := ih α r β h q heq
    exact ⟨hh, hq, qDefEq_trans henv hdt hde⟩
  | bvar | sort | app | lam | forallE | quotTy | quotMk | quotLift | eqTy | eqRefl | eqRec =>
    intro _ _ _ _ _ heq; cases heq

private theorem qHasType_eqRefl_inv {env : QEnv} (henv : QEnvClosed env) :
    ∀ {ctx α a T}, QHasType env ctx (.eqRefl α a) T ->
      QDefEq env (.eqTy α a a) T := by
  suffices hs : ∀ {ctx e T}, QHasType env ctx e T ->
      ∀ α a, e = .eqRefl α a -> QDefEq env (.eqTy α a a) T by
    intro ctx α a T hty; exact hs hty α a rfl
  intro ctx e T hty
  induction hty with
  | eqRefl _ _ =>
    intro α a heq; injection heq with h1 h2
    subst h1; subst h2; exact qDefEq_refl env _
  | conv _ hde _ ih _ =>
    intro α a heq
    exact qDefEq_trans henv (ih α a heq) hde
  | bvar | sort | app | lam | forallE | quotTy | quotMk | quotLift | quotInd | eqTy | eqRec =>
    intro _ _ heq; cases heq

private theorem qHasType_eqRec_inv {env : QEnv} (henv : QEnvClosed env) :
    ∀ {ctx α a m minor b e T}, QHasType env ctx (.eqRec α a m minor b e) T ->
      QHasType env ctx minor (.app (.app m a) (.eqRefl α a)) ∧
      QHasType env ctx e (.eqTy α a b) ∧
      QDefEq env (.app (.app m b) e) T := by
  suffices hs : ∀ {ctx term T}, QHasType env ctx term T ->
      ∀ α a m minor b e, term = .eqRec α a m minor b e ->
        QHasType env ctx minor (.app (.app m a) (.eqRefl α a)) ∧
        QHasType env ctx e (.eqTy α a b) ∧
        QDefEq env (.app (.app m b) e) T by
    intro ctx α a m minor b e T hty; exact hs hty α a m minor b e rfl
  intro ctx term T hty
  induction hty with
  | eqRec _ _ _ hminor _ he =>
    intro α a m minor b e heq; injection heq with h1 h2 h3 h4 h5 h6
    subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
    exact ⟨hminor, he, qDefEq_refl env _⟩
  | conv _ hde _ ih _ =>
    intro α a m minor b e heq
    obtain ⟨hm, he, hdt⟩ := ih α a m minor b e heq
    exact ⟨hm, he, qDefEq_trans henv hdt hde⟩
  | bvar | sort | app | lam | forallE | quotTy | quotMk | quotLift | quotInd | eqTy | eqRefl =>
    intro _ _ _ _ _ _ heq; cases heq

/-- Helper lemma allowing `QHasType` conversion when an explicit witness `Sort u`
    is provided, derived via `α_eq` for `Quot` and `Eq` soundness statements. -/
private theorem qHasType_eq_type {env ctx e T₁ T₂ u}
    (h1 : QHasType env ctx e T₁) (hde : QDefEq env T₁ T₂) (hT2 : QHasType env ctx T₂ (.sort u)) :
    QHasType env ctx e T₂ :=
  .conv h1 hde hT2

/-- **Theorem (`quotLift_sound`)**:
    `Quot.lift α r β f h (Quot.mk α' r' a) ~> f a` preserves both definitional equality
    (`QDefEq`) and dependent kernel typing (`QHasType`). -/
theorem quotLift_sound {env : QEnv} (henv : QEnvClosed env)
    {ctx : List QExpr} {α r β f h α' r' a T : QExpr} {uα uT : Nat}
    (hα : QHasType env ctx α (.sort uα))
    (hT : QHasType env ctx T (.sort uT))
    (hty : QHasType env ctx (.quotLift α r β f h (.quotMk α' r' a)) T) :
    QDefEq env (.quotLift α r β f h (.quotMk α' r' a)) (.app f a) ∧
    QHasType env ctx (.app f a) T := by
  have hred : QDefEq env (.quotLift α r β f h (.quotMk α' r' a)) (.app f a) :=
    qDefEq_of_parRed (.quotLiftRed (qParRed_refl env f) (qParRed_refl env a))
  obtain ⟨hf, hmk, hβT⟩ := qHasType_quotLift_inv henv hty
  obtain ⟨ha, hqt⟩ := qHasType_quotMk_inv henv hmk
  obtain ⟨hαeq, _⟩ := qDefEq_quotTy_inj hqt
  have ha' : QHasType env ctx a α := qHasType_eq_type ha hαeq hα
  have happ : QHasType env ctx (.app f a) ((β.shift 0 1).subst 0 a) := .app hf ha'
  have hsub : (β.shift 0 1).subst 0 a = β := by
    simpa [QExpr.shift_zero] using QExpr.subst_shift_cancel β a 0 0 0 (Nat.le_refl 0)
  rw [hsub] at happ
  exact ⟨hred, qHasType_eq_type happ hβT hT⟩

/-- **Theorem (`quotInd_sound`)**:
    `Quot.ind α r β h (Quot.mk α' r' a) ~> h a` preserves both definitional equality
    (`QDefEq`) and dependent kernel typing (`QHasType`). -/
theorem quotInd_sound {env : QEnv} (henv : QEnvClosed env)
    {ctx : List QExpr} {α r β h α' r' a T : QExpr} {uα uT : Nat}
    (hα : QHasType env ctx α (.sort uα))
    (hT : QHasType env ctx T (.sort uT))
    (hty : QHasType env ctx (.quotInd α r β h (.quotMk α' r' a)) T) :
    QDefEq env (.quotInd α r β h (.quotMk α' r' a)) (.app h a) ∧
    QHasType env ctx (.app h a) T := by
  have hred : QDefEq env (.quotInd α r β h (.quotMk α' r' a)) (.app h a) :=
    qDefEq_of_parRed (.quotIndRed (qParRed_refl env h) (qParRed_refl env a))
  obtain ⟨hh, hmk, hβT⟩ := qHasType_quotInd_inv henv hty
  obtain ⟨ha, hqt⟩ := qHasType_quotMk_inv henv hmk
  obtain ⟨hαeq, hreq⟩ := qDefEq_quotTy_inj hqt
  have ha' : QHasType env ctx a α := qHasType_eq_type ha hαeq hα
  have happ : QHasType env ctx (.app h a)
      ((QExpr.app (β.shift 0 1) (.quotMk (α.shift 0 1) (r.shift 0 1) (.bvar 0))).subst 0 a) :=
    .app hh ha'
  have hsub : (QExpr.app (β.shift 0 1) (.quotMk (α.shift 0 1) (r.shift 0 1) (.bvar 0))).subst 0 a =
      QExpr.app β (.quotMk α r a) := by
    simp only [QExpr.subst]
    have hβc : (β.shift 0 1).subst 0 a = β := by
      simpa [QExpr.shift_zero] using QExpr.subst_shift_cancel β a 0 0 0 (Nat.le_refl 0)
    have hαc : (α.shift 0 1).subst 0 a = α := by
      simpa [QExpr.shift_zero] using QExpr.subst_shift_cancel α a 0 0 0 (Nat.le_refl 0)
    have hrc : (r.shift 0 1).subst 0 a = r := by
      simpa [QExpr.shift_zero] using QExpr.subst_shift_cancel r a 0 0 0 (Nat.le_refl 0)
    simp [hβc, hαc, hrc, QExpr.shift_zero]
  rw [hsub] at happ
  have hmk_eq : QDefEq env (.quotMk α r a) (.quotMk α' r' a) :=
    qDefEq_quotMk (qDefEq_symm hαeq) (qDefEq_symm hreq) (qDefEq_refl env a)
  have hconv1 : QDefEq env (.app β (.quotMk α r a)) (.app β (.quotMk α' r' a)) :=
    qDefEq_app henv (qDefEq_refl env β) hmk_eq
  have hconv : QDefEq env (.app β (.quotMk α r a)) T := qDefEq_trans henv hconv1 hβT
  exact ⟨hred, qHasType_eq_type happ hconv hT⟩

/-- **Theorem (`eqRec_iota_sound`)**:
    Indexed `Eq.rec` reduction `Eq.rec α a motive minor b (Eq.refl α' a') ~> minor`
    preserves both definitional equality (`QDefEq`) and dependent kernel typing (`QHasType`),
    establishing soundness of `Eq.rec` iota reduction even across definitionally equal
    endpoints `b ≡ a`. -/
theorem eqRec_iota_sound {env : QEnv} (henv : QEnvClosed env)
    {ctx : List QExpr} {α a motive minor b α' a' T : QExpr} {uT : Nat}
    (hT : QHasType env ctx T (.sort uT))
    (hty : QHasType env ctx (.eqRec α a motive minor b (.eqRefl α' a')) T) :
    QDefEq env (.eqRec α a motive minor b (.eqRefl α' a')) minor ∧
    QHasType env ctx minor T := by
  have hred : QDefEq env (.eqRec α a motive minor b (.eqRefl α' a')) minor :=
    qDefEq_of_parRed (.eqRecRed (qParRed_refl env minor))
  obtain ⟨hminor, hrefl, hmT⟩ := qHasType_eqRec_inv henv hty
  have heqTy := qHasType_eqRefl_inv henv hrefl
  obtain ⟨hαeq, ha'a, ha'b⟩ := qDefEq_eqTy_inj heqTy
  have hab : QDefEq env a b := qDefEq_trans henv (qDefEq_symm ha'a) ha'b
  have hrefl_eq : QDefEq env (.eqRefl α a) (.eqRefl α' a') :=
    qDefEq_eqRefl (qDefEq_symm hαeq) (qDefEq_symm ha'a)
  have happ1 : QDefEq env (.app (.app motive a) (.eqRefl α a))
      (.app (.app motive b) (.eqRefl α' a')) :=
    qDefEq_app henv (qDefEq_app henv (qDefEq_refl env motive) hab) hrefl_eq
  have hconv : QDefEq env (.app (.app motive a) (.eqRefl α a)) T :=
    qDefEq_trans henv happ1 hmT
  exact ⟨hred, qHasType_eq_type hminor hconv hT⟩

/-- Multi-argument spine `mkAppN` helper preserving `QDefEq` and `QHasType`. -/
def qMkAppN (fn : QExpr) (args : List QExpr) : QExpr :=
  args.foldl QExpr.app fn

theorem qMkAppN_congr {env : QEnv} (henv : QEnvClosed env) {f₁ f₂ : QExpr}
    (hf : QDefEq env f₁ f₂) (args : List QExpr) :
    QDefEq env (qMkAppN f₁ args) (qMkAppN f₂ args) := by
  induction args generalizing f₁ f₂ with
  | nil => exact hf
  | cons a rest ih =>
    simp only [qMkAppN, List.foldl_cons]
    exact ih (qDefEq_app henv hf (qDefEq_refl env a))

theorem quotLift_appN_defEq {env : QEnv} (henv : QEnvClosed env)
    (α r β f h α' r' a : QExpr) (extra : List QExpr) :
    QDefEq env (qMkAppN (.quotLift α r β f h (.quotMk α' r' a)) extra)
      (qMkAppN (.app f a) extra) :=
  qMkAppN_congr henv (qDefEq_of_parRed (.quotLiftRed (qParRed_refl env f) (qParRed_refl env a))) extra

theorem quotInd_appN_defEq {env : QEnv} (henv : QEnvClosed env)
    (α r β h α' r' a : QExpr) (extra : List QExpr) :
    QDefEq env (qMkAppN (.quotInd α r β h (.quotMk α' r' a)) extra)
      (qMkAppN (.app h a) extra) :=
  qMkAppN_congr henv (qDefEq_of_parRed (.quotIndRed (qParRed_refl env h) (qParRed_refl env a))) extra

theorem eqRec_appN_defEq {env : QEnv} (henv : QEnvClosed env)
    (α a motive minor b α' a' : QExpr) (extra : List QExpr) :
    QDefEq env (qMkAppN (.eqRec α a motive minor b (.eqRefl α' a')) extra)
      (qMkAppN minor extra) :=
  qMkAppN_congr henv (qDefEq_of_parRed (.eqRecRed (qParRed_refl env minor))) extra

/-- Syntactic parameter + index arity guard matching `RecInfo.tele_arity_ok` in `con-gpu`
    `soa_pack.rs` + `typecheck_whnf.wgsl`. -/
structure IndexedIotaSpec where
  numParams : Nat
  numIndices : Nat
  fieldCount : Nat
  teleArityOk : Bool

/-- **Theorem (`indexedIota_sound`)**:
    Whenever an indexed inductive recursor checks out (`teleArityOk = true`) with
    parameter/index counts `(numParams, numIndices)` matching the major constructor spine,
    and minor application `minorApplied` has type `minorTy` definitionally equal to the
    target motive type `targetTy : Sort u`, then `minorApplied` is sound at `targetTy` and
    definitionally equal to the `iota`-reduced result. -/
theorem indexedIota_sound {env : QEnv} (_henv : QEnvClosed env) (spec : IndexedIotaSpec)
    (hok : spec.teleArityOk = true)
    {ctx : List QExpr} {minorApplied minorTy targetTy : QExpr} {u : Nat}
    (_hnum : ∀ (params indices fields : List QExpr),
      params.length = spec.numParams ->
      indices.length = spec.numIndices ->
      fields.length = spec.fieldCount ->
      params.length + indices.length + 1 = spec.numParams + spec.numIndices + 1)
    (hmin : QHasType env ctx minorApplied minorTy)
    (hde : QDefEq env minorTy targetTy)
    (htarg : QHasType env ctx targetTy (.sort u)) :
    spec.teleArityOk = true ∧ QHasType env ctx minorApplied targetTy :=
  ⟨hok, qHasType_eq_type hmin hde htarg⟩

/-! ### 5. Frozen Persistent Environment Composition (`verifiedPrefix_append_sound`) -/

/-- Every constant reference inside `e : KExpr` is strictly below `bound`. -/
def ConstClosedBelow (bound : Nat) : KExpr -> Prop
  | .bvar _ | .fvar _ | .sort _ => True
  | .const cid => cid < bound
  | .app fn arg => ConstClosedBelow bound fn ∧ ConstClosedBelow bound arg
  | .lam ty body => ConstClosedBelow bound ty ∧ ConstClosedBelow bound body
  | .forallE ty body => ConstClosedBelow bound ty ∧ ConstClosedBelow bound body
  | .letE ty val body =>
    ConstClosedBelow bound ty ∧ ConstClosedBelow bound val ∧ ConstClosedBelow bound body

theorem constClosedBelow_inst {bound : Nat} {e sub : KExpr}
    (he : ConstClosedBelow bound e) (hs : ConstClosedBelow bound sub) :
    ∀ k, ConstClosedBelow bound (e.inst k sub) := by
  induction e with
  | bvar idx =>
    intro k
    unfold KExpr.inst
    split
    · exact hs
    · trivial
  | fvar _ | sort _ => intro _; trivial
  | const cid => intro _; exact he
  | app fn arg ih1 ih2 =>
    intro k
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k, ih2 he.2 k⟩
  | lam ty body ih1 ih2 =>
    intro k
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k, ih2 he.2 (k + 1)⟩
  | forallE ty body ih1 ih2 =>
    intro k
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k, ih2 he.2 (k + 1)⟩
  | letE ty val body ih1 ih2 ih3 =>
    intro k
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k, ih2 he.2.1 k, ih3 he.2.2 (k + 1)⟩

theorem constClosedBelow_abst {bound : Nat} {e : KExpr}
    (he : ConstClosedBelow bound e) :
    ∀ k fid, ConstClosedBelow bound (e.abst k fid) := by
  induction e with
  | bvar _ => intro _ _; trivial
  | fvar id =>
    intro k fid
    unfold KExpr.abst
    split <;> trivial
  | sort _ => intro _ _; trivial
  | const cid => intro _ _; exact he
  | app fn arg ih1 ih2 =>
    intro k fid
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k fid, ih2 he.2 k fid⟩
  | lam ty body ih1 ih2 =>
    intro k fid
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k fid, ih2 he.2 (k + 1) fid⟩
  | forallE ty body ih1 ih2 =>
    intro k fid
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k fid, ih2 he.2 (k + 1) fid⟩
  | letE ty val body ih1 ih2 ih3 =>
    intro k fid
    simp only [ConstClosedBelow] at he
    exact ⟨ih1 he.1 k fid, ih2 he.2.1 k fid, ih3 he.2.2 (k + 1) fid⟩

private theorem constClosedBelow_inst_fvar {bound : Nat} {e : KExpr}
    (he : ConstClosedBelow bound e) (fid k : Nat) :
    ConstClosedBelow bound (e.inst k (.fvar fid)) :=
  @constClosedBelow_inst bound e (.fvar fid) he trivial k

/-- Every declaration in `prefixEnv` only references constant IDs `< prefixEnv.size`. -/
abbrev PrefixClosed (prefixEnv : KEnv) : Prop :=
  ∀ (cid : Nat) (d : ConstDecl), prefixEnv[cid]? = some d ->
    ConstClosedBelow prefixEnv.size d.ty ∧
    (∀ v, d.val? = some v -> ConstClosedBelow prefixEnv.size v)

private theorem array_getElem?_append_left {α : Type} (a b : Array α) {i : Nat}
    (hi : i < a.size) : (a ++ b)[i]? = a[i]? := by
  have hi2 : i < (a ++ b).size := by rw [Array.size_append]; omega
  rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi2, Array.getElem_append_left hi]

private theorem array_getElem?_append_right {α : Type} (a b : Array α) {j : Nat} :
    (a ++ b)[a.size + j]? = b[j]? := by
  by_cases hj : j < b.size
  · have hij : a.size + j < (a ++ b).size := by rw [Array.size_append]; omega
    rw [Array.getElem?_eq_getElem hij, Array.getElem?_eq_getElem hj,
      Array.getElem_append_right (Nat.le_add_right a.size j)]
    simp only [Nat.add_sub_cancel_left]
  · have hge : (a ++ b).size ≤ a.size + j := by rw [Array.size_append]; omega
    rw [Array.getElem?_eq_none hge, Array.getElem?_eq_none (Nat.le_of_not_lt hj)]

theorem whnfFuel_prefix_mono (prefixEnv suffixEnv : KEnv) (hpc : PrefixClosed prefixEnv) :
    ∀ (fuel : Nat) (e w : KExpr),
      ConstClosedBelow prefixEnv.size e ->
      whnfFuel prefixEnv fuel e = some w ->
      ConstClosedBelow prefixEnv.size w ∧
      whnfFuel (prefixEnv ++ suffixEnv) fuel e = some w
  | 0, _, _, _, h => by simp [whnfFuel] at h
  | fuel + 1, e, w, hce, h => by
    cases e with
    | bvar _ | fvar _ | sort _ | lam _ _ | forallE _ _ =>
      simp only [whnfFuel, Option.some.injEq] at h ⊢
      rw [← h]
      exact ⟨hce, rfl⟩
    | const cid =>
      have hcid : cid < prefixEnv.size := hce
      have hap := array_getElem?_append_left prefixEnv suffixEnv hcid
      simp only [whnfFuel] at h ⊢
      rw [hap]
      cases hd : prefixEnv[cid]? with
      | none =>
        rw [hd] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        exact ⟨hce, rfl⟩
      | some decl =>
        rw [hd] at h
        dsimp only at h ⊢
        cases hv : decl.val? with
        | none =>
          rw [hv] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact ⟨hce, rfl⟩
        | some body =>
          rw [hv] at h
          dsimp only at h ⊢
          have hbody : ConstClosedBelow prefixEnv.size body := (hpc cid decl hd).2 body hv
          exact whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel body w hbody h
    | letE ty val body =>
      simp only [ConstClosedBelow] at hce
      simp only [whnfFuel] at h ⊢
      exact whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel (body.inst 0 val) w
        (constClosedBelow_inst hce.2.2 hce.2.1 0) h
    | app fn arg =>
      simp only [ConstClosedBelow] at hce
      simp only [whnfFuel] at h ⊢
      cases hfn : whnfFuel prefixEnv fuel fn with
      | none => rw [hfn] at h; cases h
      | some fn' =>
        rw [hfn] at h
        have ⟨hcfn', hfn_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel fn fn' hce.1 hfn
        rw [hfn_ext]
        cases fn' with
        | lam _ body =>
          simp only [ConstClosedBelow] at hcfn'
          exact whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel (body.inst 0 arg) w
            (constClosedBelow_inst hcfn'.2 hce.2 0) h
        | bvar _ | fvar _ | sort _ | const _ | app _ _ | forallE _ _ | letE _ _ _ =>
          simp only [Option.some.injEq] at h
          rw [← h]
          exact ⟨⟨hcfn', hce.2⟩, rfl⟩

theorem defEqSpec_prefix_mono (prefixEnv suffixEnv : KEnv) (hpc : PrefixClosed prefixEnv) :
    ∀ (fuel fid : Nat) (a b : KExpr),
      ConstClosedBelow prefixEnv.size a ->
      ConstClosedBelow prefixEnv.size b ->
      defEqSpec prefixEnv fuel fid a b = true ->
      defEqSpec (prefixEnv ++ suffixEnv) fuel fid a b = true
  | 0, _, _, _, _, _, h => by simp [defEqSpec] at h
  | fuel + 1, fid, a, b, hca, hcb, h => by
    simp only [defEqSpec] at h ⊢
    by_cases heq : (a == b) = true
    · simp [heq]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hwa : whnfFuel prefixEnv fuel a with
      | none => rw [hwa] at h; cases h
      | some wa =>
        cases hwb : whnfFuel prefixEnv fuel b with
        | none => rw [hwa, hwb] at h; cases h
        | some wb =>
          rw [hwa, hwb] at h
          have ⟨hcwa, hwa_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel a wa hca hwa
          have ⟨hcwb, hwb_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel b wb hcb hwb
          rw [hwa_ext, hwb_ext]
          dsimp only at h ⊢
          cases wa <;> cases wb <;> simp only at h ⊢
          all_goals try exact h
          · simp only [Bool.and_eq_true] at h ⊢
            simp only [ConstClosedBelow] at hcwa hcwb
            exact ⟨defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel fid _ _ hcwa.1 hcwb.1 h.1,
                   defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel fid _ _ hcwa.2 hcwb.2 h.2⟩
          · simp only [Bool.and_eq_true] at h ⊢
            simp only [ConstClosedBelow] at hcwa hcwb
            exact ⟨defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel fid _ _ hcwa.1 hcwb.1 h.1,
                   defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel (fid + 1) _ _
                     (constClosedBelow_inst_fvar hcwa.2 fid 0)
                     (constClosedBelow_inst_fvar hcwb.2 fid 0) h.2⟩
          · simp only [Bool.and_eq_true] at h ⊢
            simp only [ConstClosedBelow] at hcwa hcwb
            exact ⟨defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel fid _ _ hcwa.1 hcwb.1 h.1,
                   defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel (fid + 1) _ _
                     (constClosedBelow_inst_fvar hcwa.2 fid 0)
                     (constClosedBelow_inst_fvar hcwb.2 fid 0) h.2⟩

private theorem list_getElem?_constClosed {bound : Nat} :
    ∀ {ctx : List KExpr}, (∀ t ∈ ctx, ConstClosedBelow bound t) ->
    ∀ {id : Nat} {ty : KExpr}, ctx[id]? = some ty -> ConstClosedBelow bound ty
  | [], _, _, _, h => by simp at h
  | x :: _, hctx, 0, ty, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    rw [← h]; exact hctx x (by simp)
  | _ :: xs, hctx, id + 1, ty, h => by
    simp only [List.getElem?_cons_succ] at h
    exact list_getElem?_constClosed (fun t ht => hctx t (by simp [ht])) h

private theorem list_append_constClosed {bound : Nat} {ctx : List KExpr} {d : KExpr}
    (hctx : ∀ t ∈ ctx, ConstClosedBelow bound t) (hd : ConstClosedBelow bound d) :
    ∀ t ∈ ctx ++ [d], ConstClosedBelow bound t := by
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with h | h
  · exact hctx t h
  · rw [h]; exact hd

theorem inferSpec_prefix_mono (prefixEnv suffixEnv : KEnv) (hpc : PrefixClosed prefixEnv) :
    ∀ (fuel : Nat) (ctx : List KExpr) (e ty : KExpr),
      (∀ t ∈ ctx, ConstClosedBelow prefixEnv.size t) ->
      ConstClosedBelow prefixEnv.size e ->
      inferSpec prefixEnv fuel ctx e = some ty ->
      ConstClosedBelow prefixEnv.size ty ∧
      inferSpec (prefixEnv ++ suffixEnv) fuel ctx e = some ty
  | 0, _, _, _, _, _, h => by simp [inferSpec] at h
  | fuel + 1, ctx, e, ty, hctx, hce, h => by
    cases e with
    | bvar _ => simp [inferSpec] at h
    | fvar id =>
      simp only [inferSpec] at h ⊢
      exact ⟨list_getElem?_constClosed hctx h, h⟩
    | sort lvl =>
      simp only [inferSpec, Option.some.injEq] at h ⊢
      rw [← h]
      exact ⟨trivial, rfl⟩
    | const cid =>
      have hcid : cid < prefixEnv.size := hce
      have hap := array_getElem?_append_left prefixEnv suffixEnv hcid
      simp only [inferSpec] at h ⊢
      rw [hap]
      cases hd : prefixEnv[cid]? with
      | none => rw [hd] at h; simp at h
      | some d =>
        rw [hd] at h
        simp only [Option.map_some, Option.some.injEq] at h ⊢
        rw [← h]
        exact ⟨(hpc cid d hd).1, rfl⟩
    | app fn arg =>
      simp only [ConstClosedBelow] at hce
      simp only [inferSpec] at h ⊢
      cases hf : inferSpec prefixEnv fuel ctx fn with
      | none => rw [hf] at h; cases h
      | some fty =>
        rw [hf] at h
        cases ha : inferSpec prefixEnv fuel ctx arg with
        | none => rw [ha] at h; cases h
        | some aty =>
          rw [ha] at h
          have ⟨hcfty, hf_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx fn fty hctx hce.1 hf
          have ⟨hcaty, ha_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx arg aty hctx hce.2 ha
          rw [hf_ext, ha_ext]
          dsimp only at h ⊢
          cases hw : whnfFuel prefixEnv fuel fty with
          | none => rw [hw] at h; cases h
          | some w =>
            rw [hw] at h
            have ⟨hcw, hw_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel fty w hcfty hw
            rw [hw_ext]
            cases w with
            | forallE dom cod =>
              simp only [ConstClosedBelow] at hcw
              dsimp only at h ⊢
              split at h
              · next hde =>
                rw [defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx.length aty dom hcaty hcw.1 hde]
                simp only [↓reduceIte, Option.some.injEq] at h ⊢
                rw [← h]
                exact ⟨constClosedBelow_inst hcw.2 hce.2 0, rfl⟩
              · cases h
            | bvar _ | fvar _ | sort _ | const _ | app _ _ | lam _ _ | letE _ _ _ => cases h
    | lam dom body =>
      simp only [ConstClosedBelow] at hce
      simp only [inferSpec] at h ⊢
      cases hd : inferSpec prefixEnv fuel ctx dom with
      | none => rw [hd] at h; cases h
      | some domTy =>
        rw [hd] at h
        have ⟨hcdomTy, hd_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx dom domTy hctx hce.1 hd
        rw [hd_ext]
        dsimp only at h ⊢
        cases hw : whnfFuel prefixEnv fuel domTy with
        | none => rw [hw] at h; cases h
        | some w =>
          rw [hw] at h
          have ⟨_, hw_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel domTy w hcdomTy hw
          rw [hw_ext]
          cases w with
          | sort u =>
            dsimp only at h ⊢
            have hctx' := list_append_constClosed hctx hce.1
            have hb_in := constClosedBelow_inst_fvar hce.2 ctx.length 0
            cases hb : inferSpec prefixEnv fuel (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) with
            | none => rw [hb] at h; cases h
            | some bty =>
              rw [hb] at h
              have ⟨hcbty, hb_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel
                (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) bty hctx' hb_in hb
              rw [hb_ext]
              simp only [Option.some.injEq] at h ⊢
              rw [← h]
              exact ⟨⟨hce.1, constClosedBelow_abst hcbty 0 ctx.length⟩, rfl⟩
          | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h
    | forallE dom body =>
      simp only [ConstClosedBelow] at hce
      simp only [inferSpec] at h ⊢
      cases hd : inferSpec prefixEnv fuel ctx dom with
      | none => rw [hd] at h; cases h
      | some domTy =>
        rw [hd] at h
        have ⟨hcdomTy, hd_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx dom domTy hctx hce.1 hd
        rw [hd_ext]
        dsimp only at h ⊢
        cases hw : whnfFuel prefixEnv fuel domTy with
        | none => rw [hw] at h; cases h
        | some w =>
          rw [hw] at h
          have ⟨_, hw_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel domTy w hcdomTy hw
          rw [hw_ext]
          cases w with
          | sort u =>
            dsimp only at h ⊢
            have hctx' := list_append_constClosed hctx hce.1
            have hb_in := constClosedBelow_inst_fvar hce.2 ctx.length 0
            cases hb : inferSpec prefixEnv fuel (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) with
            | none => rw [hb] at h; cases h
            | some bty =>
              rw [hb] at h
              have ⟨hcbty, hb_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel
                (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) bty hctx' hb_in hb
              rw [hb_ext]
              dsimp only at h ⊢
              cases hwb : whnfFuel prefixEnv fuel bty with
              | none => rw [hwb] at h; cases h
              | some wb =>
                rw [hwb] at h
                have ⟨_, hwb_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel bty wb hcbty hwb
                rw [hwb_ext]
                cases wb with
                | sort v =>
                  simp only [Option.some.injEq] at h ⊢
                  rw [← h]
                  exact ⟨trivial, rfl⟩
                | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ =>
                  cases h
          | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h
    | letE tyExpr val body =>
      simp only [ConstClosedBelow] at hce
      simp only [inferSpec] at h ⊢
      cases ht : inferSpec prefixEnv fuel ctx tyExpr with
      | none => rw [ht] at h; cases h
      | some tyTy =>
        rw [ht] at h
        cases hv : inferSpec prefixEnv fuel ctx val with
        | none => rw [hv] at h; cases h
        | some valTy =>
          rw [hv] at h
          have ⟨hctyTy, ht_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx tyExpr tyTy hctx hce.1 ht
          have ⟨hcvalTy, hv_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx val valTy hctx hce.2.1 hv
          rw [ht_ext, hv_ext]
          dsimp only at h ⊢
          cases hw : whnfFuel prefixEnv fuel tyTy with
          | none => rw [hw] at h; cases h
          | some w =>
            rw [hw] at h
            have ⟨_, hw_ext⟩ := whnfFuel_prefix_mono prefixEnv suffixEnv hpc fuel tyTy w hctyTy hw
            rw [hw_ext]
            cases w with
            | sort u =>
              dsimp only at h ⊢
              split at h
              · next hde =>
                rw [defEqSpec_prefix_mono prefixEnv suffixEnv hpc fuel ctx.length valTy tyExpr
                  hcvalTy hce.1 hde]
                simp only [↓reduceIte]
                have hctx' := list_append_constClosed hctx hce.1
                have hb_in := constClosedBelow_inst_fvar hce.2.2 ctx.length 0
                cases hb : inferSpec prefixEnv fuel (ctx ++ [tyExpr])
                    (body.inst 0 (.fvar ctx.length)) with
                | none => rw [hb] at h; cases h
                | some bty =>
                  rw [hb] at h
                  have ⟨hcbty, hb_ext⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc fuel
                    (ctx ++ [tyExpr]) (body.inst 0 (.fvar ctx.length)) bty hctx' hb_in hb
                  rw [hb_ext]
                  simp only [Option.some.injEq] at h ⊢
                  rw [← h]
                  exact ⟨⟨hce.1, hce.2.1, constClosedBelow_abst hcbty 0 ctx.length⟩, rfl⟩
              · cases h
            | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h

/-- Kernel verification condition for a single declaration inside environment `env`. -/
def DeclVerified (env : KEnv) (d : ConstDecl) : Prop :=
  (∃ f1 u, inferSpec env f1 [] d.ty = some (.sort u)) ∧
  (match d.val? with
   | none => True
   | some val => ∃ f2 vty f3, inferSpec env f2 [] val = some vty ∧ defEqSpec env f3 0 vty d.ty = true)

/-- Every declaration in `env` satisfies `DeclVerified env d`. -/
abbrev VerifiedEnv (env : KEnv) : Prop :=
  ∀ (cid : Nat) (d : ConstDecl), env[cid]? = some d -> DeclVerified env d

/-- Every suffix declaration `d ∈ decls[k..n]` is verified against the composed frozen
    prefix environment `prefixEnv ++ suffixEnv`. -/
abbrev VerifiedSuffix (prefixEnv suffixEnv : KEnv) : Prop :=
  ∀ (j : Nat) (d : ConstDecl), suffixEnv[j]? = some d -> DeclVerified (prefixEnv ++ suffixEnv) d

/-- **Theorem (`verifiedPrefix_append_sound`)**:
    Given a frozen, constant-closed, verified persistent prefix `prefixEnv = decls[0..k]`
    and a suffix `suffixEnv = decls[k..n]` verified against `prefixEnv ++ suffixEnv`,
    the entire combined environment `prefixEnv ++ suffixEnv = decls[0..n]` satisfies
    `VerifiedEnv` and every declaration `d` in `decls[0..n]` obeys the declarative
    `HasType` typing judgment (together with `EnvSound` persistence when backed by GPU
    persistent tables `gpuPrefix ++ gpuSuffix`). -/
theorem verifiedPrefix_append_sound
    (pers : SoATier) (gpuPrefix gpuSuffix : Array GpuConstDecl)
    (prefixEnv suffixEnv : KEnv)
    (hpc : PrefixClosed prefixEnv)
    (hpre : VerifiedEnv prefixEnv)
    (hsuf : VerifiedSuffix prefixEnv suffixEnv)
    (henv : EnvSound pers (gpuPrefix ++ gpuSuffix) (prefixEnv ++ suffixEnv)) :
    let fullEnv := prefixEnv ++ suffixEnv
    EnvSound pers (gpuPrefix ++ gpuSuffix) fullEnv ∧
    VerifiedEnv fullEnv ∧
    (∀ (cid : Nat) (d : ConstDecl), fullEnv[cid]? = some d ->
      (∃ u, HasType fullEnv [] d.ty (.sort u)) ∧
      (∀ val, d.val? = some val ->
        ∃ vty f3, HasType fullEnv [] val vty ∧ defEqSpec fullEnv f3 0 vty d.ty = true)) := by
  dsimp only
  have hver : VerifiedEnv (prefixEnv ++ suffixEnv) := by
    intro cid d hlu
    by_cases hlt : cid < prefixEnv.size
    · have hlu_pre : prefixEnv[cid]? = some d := by
        rwa [array_getElem?_append_left prefixEnv suffixEnv hlt] at hlu
      have hd_pre := hpre cid d hlu_pre
      have hclose := hpc cid d hlu_pre
      rcases hd_pre with ⟨⟨f1, u, hty⟩, hval⟩
      refine ⟨⟨f1, u, ?_⟩, ?_⟩
      · exact (inferSpec_prefix_mono prefixEnv suffixEnv hpc f1 [] d.ty (.sort u)
          (fun _ hm => by simp at hm) hclose.1 hty).2
      · cases hv : d.val? with
        | none => trivial
        | some val =>
          rw [hv] at hval
          rcases hval with ⟨f2, vty, f3, hvi, hde⟩
          have ⟨hcvty, hvi'⟩ := inferSpec_prefix_mono prefixEnv suffixEnv hpc f2 [] val vty
            (fun _ hm => by simp at hm) (hclose.2 val hv) hvi
          have hde' := defEqSpec_prefix_mono prefixEnv suffixEnv hpc f3 0 vty d.ty
            hcvty hclose.1 hde
          exact ⟨f2, vty, f3, hvi', hde'⟩
    · have hcid : cid = prefixEnv.size + (cid - prefixEnv.size) := by omega
      rw [hcid, array_getElem?_append_right] at hlu
      exact hsuf (cid - prefixEnv.size) d hlu
  refine ⟨henv, hver, ?_⟩
  intro cid d hlu
  obtain ⟨⟨f1, u, hty⟩, hval⟩ := hver cid d hlu
  refine ⟨⟨u, inferSpec_hasType (prefixEnv ++ suffixEnv) f1 [] d.ty (.sort u) hty⟩, ?_⟩
  intro val hv
  rw [hv] at hval
  rcases hval with ⟨f2, vty, f3, hvi, hde⟩
  exact ⟨vty, f3, inferSpec_hasType (prefixEnv ++ suffixEnv) f2 [] val vty hvi, hde⟩

end ConGpuProof
