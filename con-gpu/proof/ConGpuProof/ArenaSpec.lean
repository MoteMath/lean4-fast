/-
ConGpuProof.ArenaSpec
=====================
Formal specification of con-gpu's 32-bit `EIdx` two-tier SoA expression arena
(`PersTier` immutable shared array + `ScratchTier` per-thread bump array) and
functional Lean kernel reduction/typing specification (`whnfFuel`, `defEqSpec`,
`inferSpec`).
-/

namespace ConGpuProof

/-! ### 1. Bit-packed 32-bit `EIdx` Handles (Pure Linear Arithmetic) -/

def tierP : UInt32 := 0
def tierS : UInt32 := 1
def idxCap : UInt32 := 67108864     -- 2^26
def wideCap : UInt32 := 1073741824  -- 2^30
def tierSpan : UInt32 := 2147483648 -- 2^31

def etagBVar : UInt32 := 0
def etagFVar : UInt32 := 1
def etagSort : UInt32 := 2
def etagConst : UInt32 := 3
def etagApp : UInt32 := 4
def etagLam : UInt32 := 5
def etagForall : UInt32 := 6
def etagLet : UInt32 := 7

/-- 32-bit packed handle matching `con-ron-core/src/arena/handle.rs`. -/
structure EIdx where
  word : UInt32
  deriving DecidableEq, Repr, BEq, Inhabited

namespace EIdx

def pack (tag tier idx : UInt32) : EIdx :=
  ⟨tier * tierSpan + tag * idxCap + idx⟩

def packWide (tier idx : UInt32) : EIdx :=
  ⟨tier * tierSpan + wideCap + idx⟩

def isWide (e : EIdx) : Bool :=
  (e.word / wideCap) % 2 == 1

def tier (e : EIdx) : UInt32 :=
  e.word / tierSpan

def isPers (e : EIdx) : Bool :=
  e.tier == tierP

def tag (e : EIdx) : UInt32 :=
  if e.isWide then etagApp else (e.word / idxCap) % 16

def index (e : EIdx) : UInt32 :=
  if e.isWide then e.word % wideCap else e.word % idxCap

private theorem pack_word_eq {tag tier idx : UInt32}
    (ht : tier < 2) (hg : tag < 16) (hi : idx < idxCap) :
    (pack tag tier idx).word.toNat =
      tier.toNat * 2147483648 + tag.toNat * 67108864 + idx.toNat := by
  have ht' : tier.toNat < 2 := ht
  have hg' : tag.toNat < 16 := hg
  have hi' : idx.toNat < 67108864 := hi
  unfold pack tierSpan idxCap
  simp only [UInt32.toNat_add, UInt32.toNat_mul]
  change ((((tier.toNat * 2147483648) % 4294967296 +
      (tag.toNat * 67108864) % 4294967296) % 4294967296) + idx.toNat) % 4294967296 = _
  omega

private theorem packWide_word_eq {tier idx : UInt32}
    (ht : tier < 2) (hi : idx < wideCap) :
    (packWide tier idx).word.toNat =
      tier.toNat * 2147483648 + 1073741824 + idx.toNat := by
  have ht' : tier.toNat < 2 := ht
  have hi' : idx.toNat < 1073741824 := hi
  unfold packWide tierSpan wideCap
  simp only [UInt32.toNat_add, UInt32.toNat_mul]
  change ((((tier.toNat * 2147483648) % 4294967296 + 1073741824) % 4294967296) +
      idx.toNat) % 4294967296 = _
  omega

theorem isWide_pack {tag tier idx : UInt32}
    (ht : tier < 2) (hg : tag < 16) (hi : idx < idxCap) :
    (pack tag tier idx).isWide = false := by
  have hw := pack_word_eq ht hg hi
  have ht' : tier.toNat < 2 := ht
  have hg' : tag.toNat < 16 := hg
  have hi' : idx.toNat < 67108864 := hi
  unfold isWide wideCap
  rw [beq_eq_false_iff_ne]
  intro heq
  have h0 : ((pack tag tier idx).word / 1073741824 % 2).toNat = 1 :=
    congrArg UInt32.toNat heq
  simp only [UInt32.toNat_mod, UInt32.toNat_div] at h0
  rw [hw] at h0
  change (tier.toNat * 2147483648 + tag.toNat * 67108864 + idx.toNat) /
      1073741824 % 2 = 1 at h0
  omega

theorem isWide_packWide {tier idx : UInt32}
    (ht : tier < 2) (hi : idx < wideCap) :
    (packWide tier idx).isWide = true := by
  have hw := packWide_word_eq ht hi
  have ht' : tier.toNat < 2 := ht
  have hi' : idx.toNat < 1073741824 := hi
  unfold isWide wideCap
  rw [beq_iff_eq]
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_mod, UInt32.toNat_div]
  rw [hw]
  change (tier.toNat * 2147483648 + 1073741824 + idx.toNat) / 1073741824 % 2 = 1
  omega

theorem tier_pack {tag tier idx : UInt32}
    (ht : tier < 2) (hg : tag < 16) (hi : idx < idxCap) :
    (pack tag tier idx).tier = tier := by
  have hw := pack_word_eq ht hg hi
  have ht' : tier.toNat < 2 := ht
  have hg' : tag.toNat < 16 := hg
  have hi' : idx.toNat < 67108864 := hi
  apply UInt32.toNat_inj.mp
  unfold EIdx.tier tierSpan
  simp only [UInt32.toNat_div]
  rw [hw]
  change (tier.toNat * 2147483648 + tag.toNat * 67108864 + idx.toNat) / 2147483648 =
    tier.toNat
  omega

theorem tag_pack {tag tier idx : UInt32}
    (ht : tier < 2) (hg : tag < 16) (hi : idx < idxCap) :
    (pack tag tier idx).tag = tag := by
  have hnw := isWide_pack ht hg hi
  have hw := pack_word_eq ht hg hi
  have ht' : tier.toNat < 2 := ht
  have hg' : tag.toNat < 16 := hg
  have hi' : idx.toNat < 67108864 := hi
  unfold EIdx.tag
  rw [hnw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply UInt32.toNat_inj.mp
  unfold idxCap
  simp only [UInt32.toNat_mod, UInt32.toNat_div]
  rw [hw]
  change (tier.toNat * 2147483648 + tag.toNat * 67108864 + idx.toNat) /
      67108864 % 16 = tag.toNat
  omega

theorem index_pack {tag tier idx : UInt32}
    (ht : tier < 2) (hg : tag < 16) (hi : idx < idxCap) :
    (pack tag tier idx).index = idx := by
  have hnw := isWide_pack ht hg hi
  have hw := pack_word_eq ht hg hi
  have ht' : tier.toNat < 2 := ht
  have hg' : tag.toNat < 16 := hg
  have hi' : idx.toNat < 67108864 := hi
  unfold EIdx.index
  rw [hnw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply UInt32.toNat_inj.mp
  unfold idxCap
  simp only [UInt32.toNat_mod]
  rw [hw]
  change (tier.toNat * 2147483648 + tag.toNat * 67108864 + idx.toNat) % 67108864 =
    idx.toNat
  omega

theorem tier_packWide {tier idx : UInt32}
    (ht : tier < 2) (hi : idx < wideCap) :
    (packWide tier idx).tier = tier := by
  have hw := packWide_word_eq ht hi
  have ht' : tier.toNat < 2 := ht
  have hi' : idx.toNat < 1073741824 := hi
  apply UInt32.toNat_inj.mp
  unfold EIdx.tier tierSpan
  simp only [UInt32.toNat_div]
  rw [hw]
  change (tier.toNat * 2147483648 + 1073741824 + idx.toNat) / 2147483648 = tier.toNat
  omega

theorem tag_packWide {tier idx : UInt32}
    (ht : tier < 2) (hi : idx < wideCap) :
    (packWide tier idx).tag = etagApp := by
  unfold EIdx.tag
  rw [isWide_packWide ht hi]
  rfl

theorem index_packWide {tier idx : UInt32}
    (ht : tier < 2) (hi : idx < wideCap) :
    (packWide tier idx).index = idx := by
  have hw := packWide_word_eq ht hi
  have hi' : idx.toNat < 1073741824 := hi
  have ht' : tier.toNat < 2 := ht
  unfold EIdx.index
  rw [isWide_packWide ht hi]
  simp only [↓reduceIte]
  apply UInt32.toNat_inj.mp
  unfold wideCap
  simp only [UInt32.toNat_mod]
  rw [hw]
  change (tier.toNat * 2147483648 + 1073741824 + idx.toNat) % 1073741824 = idx.toNat
  omega

end EIdx

/-! ### 2. Structure-of-Arrays (SoA) Tier Storage and Two-Tier Arena Lookup -/

/-- Decoded expression cell read out of an SoA tier. -/
inductive ExprCell where
  | bvar (idx : UInt32)
  | fvar (id : UInt32)
  | sort (lvl : UInt32)
  | const (cid : UInt32)
  | app (fn arg : EIdx)
  | lam (ty body : EIdx)
  | forallE (ty body : EIdx)
  | letE (ty val body : EIdx)
  deriving DecidableEq, Repr, Inhabited

/-- Structure-of-Arrays column storage for one tier (`PersTier` or `ScratchTier`). -/
structure SoATier where
  bvars : Array UInt32 := #[]
  fvars : Array UInt32 := #[]
  sorts : Array UInt32 := #[]
  consts : Array UInt32 := #[]
  appFn : Array EIdx := #[]
  appArg : Array EIdx := #[]
  lamTy : Array EIdx := #[]
  lamBody : Array EIdx := #[]
  forallTy : Array EIdx := #[]
  forallBody : Array EIdx := #[]
  letTy : Array EIdx := #[]
  letVal : Array EIdx := #[]
  letBody : Array EIdx := #[]
  deriving Repr, Inhabited

namespace SoATier

def empty : SoATier := {}

def totalNodes (t : SoATier) : Nat :=
  t.bvars.size + t.fvars.size + t.sorts.size + t.consts.size +
  t.appFn.size + t.lamTy.size + t.forallTy.size + t.letTy.size

def read (t : SoATier) (e : EIdx) : Option ExprCell :=
  if e.isWide then
    match t.appFn[e.index.toNat]?, t.appArg[e.index.toNat]? with
    | some fn, some arg => some (.app fn arg)
    | _, _ => none
  else
    let tg := e.tag
    if tg == etagBVar then
      t.bvars[e.index.toNat]?.map .bvar
    else if tg == etagFVar then
      t.fvars[e.index.toNat]?.map .fvar
    else if tg == etagSort then
      t.sorts[e.index.toNat]?.map .sort
    else if tg == etagConst then
      t.consts[e.index.toNat]?.map .const
    else if tg == etagLam then
      match t.lamTy[e.index.toNat]?, t.lamBody[e.index.toNat]? with
      | some ty, some b => some (.lam ty b)
      | _, _ => none
    else if tg == etagForall then
      match t.forallTy[e.index.toNat]?, t.forallBody[e.index.toNat]? with
      | some ty, some b => some (.forallE ty b)
      | _, _ => none
    else if tg == etagLet then
      match t.letTy[e.index.toNat]?, t.letVal[e.index.toNat]?, t.letBody[e.index.toNat]? with
      | some ty, some v, some b => some (.letE ty v b)
      | _, _, _ => none
    else
      none

def pushBVar (t : SoATier) (tier idx : UInt32) : SoATier × EIdx :=
  let pos := UInt32.ofNat t.bvars.size
  ({ t with bvars := t.bvars.push idx }, EIdx.pack etagBVar tier pos)

def pushFVar (t : SoATier) (tier id : UInt32) : SoATier × EIdx :=
  let pos := UInt32.ofNat t.fvars.size
  ({ t with fvars := t.fvars.push id }, EIdx.pack etagFVar tier pos)

def pushSort (t : SoATier) (tier lvl : UInt32) : SoATier × EIdx :=
  let pos := UInt32.ofNat t.sorts.size
  ({ t with sorts := t.sorts.push lvl }, EIdx.pack etagSort tier pos)

def pushConst (t : SoATier) (tier cid : UInt32) : SoATier × EIdx :=
  let pos := UInt32.ofNat t.consts.size
  ({ t with consts := t.consts.push cid }, EIdx.pack etagConst tier pos)

def pushApp (t : SoATier) (tier : UInt32) (fn arg : EIdx) : SoATier × EIdx :=
  let pos := UInt32.ofNat (min t.appFn.size t.appArg.size)
  let t' := { t with appFn := t.appFn.push fn, appArg := t.appArg.push arg }
  (t', EIdx.packWide tier pos)

def pushLam (t : SoATier) (tier : UInt32) (ty body : EIdx) : SoATier × EIdx :=
  let pos := UInt32.ofNat (min t.lamTy.size t.lamBody.size)
  let t' := { t with lamTy := t.lamTy.push ty, lamBody := t.lamBody.push body }
  (t', EIdx.pack etagLam tier pos)

def pushForall (t : SoATier) (tier : UInt32) (ty body : EIdx) : SoATier × EIdx :=
  let pos := UInt32.ofNat (min t.forallTy.size t.forallBody.size)
  let t' := { t with forallTy := t.forallTy.push ty, forallBody := t.forallBody.push body }
  (t', EIdx.pack etagForall tier pos)

def pushLet (t : SoATier) (tier : UInt32) (ty val body : EIdx) : SoATier × EIdx :=
  let pos := UInt32.ofNat (min t.letTy.size (min t.letVal.size t.letBody.size))
  let t' :=
    { t with
      letTy := t.letTy.push ty
      letVal := t.letVal.push val
      letBody := t.letBody.push body }
  (t', EIdx.pack etagLet tier pos)

def pushCell (t : SoATier) (tier : UInt32) : ExprCell -> SoATier × EIdx
  | .bvar idx => t.pushBVar tier idx
  | .fvar id => t.pushFVar tier id
  | .sort lvl => t.pushSort tier lvl
  | .const cid => t.pushConst tier cid
  | .app fn arg => t.pushApp tier fn arg
  | .lam ty body => t.pushLam tier ty body
  | .forallE ty body => t.pushForall tier ty body
  | .letE ty val body => t.pushLet tier ty val body

end SoATier

/-- Two-tier arena combining immutable `PersTier` and per-thread `ScratchTier`. -/
structure Arena where
  pers : SoATier
  scr : SoATier
  deriving Repr, Inhabited

def Arena.lookupNode (pers scr : SoATier) (e : EIdx) : Option ExprCell :=
  if e.isPers then pers.read e else scr.read e

/-- Declarative expression syntax tree corresponding to decoded arena handles. -/
inductive KExpr where
  | bvar (idx : Nat)
  | fvar (id : Nat)
  | sort (lvl : Nat)
  | const (cid : Nat)
  | app (fn arg : KExpr)
  | lam (ty body : KExpr)
  | forallE (ty body : KExpr)
  | letE (ty val body : KExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Fuel-bounded recursive decoding of a 32-bit `EIdx` in a two-tier arena. -/
def decodeExpr (pers scr : SoATier) : Nat -> EIdx -> Option KExpr
  | 0, _ => none
  | fuel + 1, e =>
    match Arena.lookupNode pers scr e with
    | none => none
    | some (.bvar idx) => some (.bvar idx.toNat)
    | some (.fvar id) => some (.fvar id.toNat)
    | some (.sort lvl) => some (.sort lvl.toNat)
    | some (.const cid) => some (.const cid.toNat)
    | some (.app fn arg) =>
      match decodeExpr pers scr fuel fn, decodeExpr pers scr fuel arg with
      | some kfn, some karg => some (.app kfn karg)
      | _, _ => none
    | some (.lam ty body) =>
      match decodeExpr pers scr fuel ty, decodeExpr pers scr fuel body with
      | some kty, some kbody => some (.lam kty kbody)
      | _, _ => none
    | some (.forallE ty body) =>
      match decodeExpr pers scr fuel ty, decodeExpr pers scr fuel body with
      | some kty, some kbody => some (.forallE kty kbody)
      | _, _ => none
    | some (.letE ty val body) =>
      match decodeExpr pers scr fuel ty, decodeExpr pers scr fuel val,
          decodeExpr pers scr fuel body with
      | some kty, some kval, some kbody => some (.letE kty kval kbody)
      | _, _, _ => none

/-- Monotone array prefix extension helper. -/
def ArrayExtends {α : Type} (a b : Array α) : Prop :=
  ∀ (i : Nat) (v : α), a[i]? = some v -> b[i]? = some v

theorem arrayExtends_refl {α : Type} (a : Array α) : ArrayExtends a a := by
  unfold ArrayExtends
  intro i v h
  exact h

theorem arrayExtends_trans {α : Type} {a b c : Array α}
    (h1 : ArrayExtends a b) (h2 : ArrayExtends b c) : ArrayExtends a c := by
  unfold ArrayExtends at h1 h2 ⊢
  intro i v h
  exact h2 i v (h1 i v h)

theorem arrayExtends_push {α : Type} (a : Array α) (x : α) :
    ArrayExtends a (a.push x) := by
  unfold ArrayExtends
  intro i v h
  by_cases hi : i < a.size
  · have h1 : a[i]? = some a[i] := Array.getElem?_eq_getElem hi
    have hval : a[i] = v := by rw [h1] at h; exact Option.some.inj h
    have hi2 : i < (a.push x).size := by rw [Array.size_push]; exact Nat.lt_succ_of_lt hi
    rw [Array.getElem?_eq_getElem hi2, Array.getElem_push_lt hi, hval]
  · have hle : a.size ≤ i := Nat.le_of_not_lt hi
    have hnone : a[i]? = none := Array.getElem?_eq_none hle
    rw [hnone] at h
    cases h

/-- Bump-allocation extension relation on `SoATier` columns. -/
structure TierExtends (s s' : SoATier) : Prop where
  bvars : ArrayExtends s.bvars s'.bvars
  fvars : ArrayExtends s.fvars s'.fvars
  sorts : ArrayExtends s.sorts s'.sorts
  consts : ArrayExtends s.consts s'.consts
  appFn : ArrayExtends s.appFn s'.appFn
  appArg : ArrayExtends s.appArg s'.appArg
  lamTy : ArrayExtends s.lamTy s'.lamTy
  lamBody : ArrayExtends s.lamBody s'.lamBody
  forallTy : ArrayExtends s.forallTy s'.forallTy
  forallBody : ArrayExtends s.forallBody s'.forallBody
  letTy : ArrayExtends s.letTy s'.letTy
  letVal : ArrayExtends s.letVal s'.letVal
  letBody : ArrayExtends s.letBody s'.letBody

theorem tierExtends_refl (s : SoATier) : TierExtends s s :=
  ⟨arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
   arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
   arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
   arrayExtends_refl _⟩

theorem tierExtends_trans {s₁ s₂ s₃ : SoATier}
    (h1 : TierExtends s₁ s₂) (h2 : TierExtends s₂ s₃) : TierExtends s₁ s₃ :=
  ⟨arrayExtends_trans h1.bvars h2.bvars,
   arrayExtends_trans h1.fvars h2.fvars,
   arrayExtends_trans h1.sorts h2.sorts,
   arrayExtends_trans h1.consts h2.consts,
   arrayExtends_trans h1.appFn h2.appFn,
   arrayExtends_trans h1.appArg h2.appArg,
   arrayExtends_trans h1.lamTy h2.lamTy,
   arrayExtends_trans h1.lamBody h2.lamBody,
   arrayExtends_trans h1.forallTy h2.forallTy,
   arrayExtends_trans h1.forallBody h2.forallBody,
   arrayExtends_trans h1.letTy h2.letTy,
   arrayExtends_trans h1.letVal h2.letVal,
   arrayExtends_trans h1.letBody h2.letBody⟩

theorem pushCell_extends (s : SoATier) (tier : UInt32) (c : ExprCell) :
    TierExtends s (s.pushCell tier c).1 := by
  cases c with
  | bvar idx =>
    exact ⟨arrayExtends_push _ _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _⟩
  | fvar id =>
    exact ⟨arrayExtends_refl _, arrayExtends_push _ _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _⟩
  | sort lvl =>
    exact ⟨arrayExtends_refl _, arrayExtends_refl _, arrayExtends_push _ _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _⟩
  | const cid =>
    exact ⟨arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_push _ _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _⟩
  | app fn arg =>
    exact ⟨arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_push _ _, arrayExtends_push _ _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _⟩
  | lam ty b =>
    exact ⟨arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_push _ _, arrayExtends_push _ _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _⟩
  | forallE ty b =>
    exact ⟨arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_push _ _, arrayExtends_push _ _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _⟩
  | letE ty v b =>
    exact ⟨arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _, arrayExtends_refl _,
      arrayExtends_refl _, arrayExtends_refl _, arrayExtends_push _ _, arrayExtends_push _ _,
      arrayExtends_push _ _⟩

theorem tierRead_extends {s s' : SoATier} (hex : TierExtends s s')
    {e : EIdx} {c : ExprCell} (hr : s.read e = some c) :
    s'.read e = some c := by
  unfold SoATier.read at hr ⊢
  dsimp only at hr ⊢
  split at hr
  · next hw =>
    simp only [hw, ↓reduceIte]
    cases h1 : s.appFn[e.index.toNat]? <;> rw [h1] at hr
    · cases hr
    cases h2 : s.appArg[e.index.toNat]? <;> rw [h2] at hr
    · cases hr
    dsimp only at hr
    simp only [Option.some.injEq] at hr
    rw [hex.appFn _ _ h1, hex.appArg _ _ h2, ← hr]
  · next hw =>
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    split at hr
    · next htag =>
      simp only [htag, ↓reduceIte]
      cases h1 : s.bvars[e.index.toNat]? <;> rw [h1] at hr
      · simp at hr
      · simp only [Option.map_some, Option.some.injEq] at hr
        rw [hex.bvars _ _ h1, Option.map_some, hr]
    · split at hr
      · next htag1 htag2 =>
        simp only [htag1, htag2, Bool.false_eq_true, ↓reduceIte]
        cases h1 : s.fvars[e.index.toNat]? <;> rw [h1] at hr
        · simp at hr
        · simp only [Option.map_some, Option.some.injEq] at hr
          rw [hex.fvars _ _ h1, Option.map_some, hr]
      · split at hr
        · next htag1 htag2 htag3 =>
          simp only [htag1, htag2, htag3, Bool.false_eq_true, ↓reduceIte]
          cases h1 : s.sorts[e.index.toNat]? <;> rw [h1] at hr
          · simp at hr
          · simp only [Option.map_some, Option.some.injEq] at hr
            rw [hex.sorts _ _ h1, Option.map_some, hr]
        · split at hr
          · next htag1 htag2 htag3 htag4 =>
            simp only [htag1, htag2, htag3, htag4, Bool.false_eq_true, ↓reduceIte]
            cases h1 : s.consts[e.index.toNat]? <;> rw [h1] at hr
            · simp at hr
            · simp only [Option.map_some, Option.some.injEq] at hr
              rw [hex.consts _ _ h1, Option.map_some, hr]
          · split at hr
            · next htag1 htag2 htag3 htag4 htag5 =>
              simp only [htag1, htag2, htag3, htag4, htag5, Bool.false_eq_true, ↓reduceIte]
              cases h1 : s.lamTy[e.index.toNat]? <;> rw [h1] at hr
              · simp at hr
              cases h2 : s.lamBody[e.index.toNat]? <;> rw [h2] at hr
              · simp at hr
              dsimp only at hr
              simp only [Option.some.injEq] at hr
              rw [hex.lamTy _ _ h1, hex.lamBody _ _ h2, ← hr]
            · split at hr
              · next htag1 htag2 htag3 htag4 htag5 htag6 =>
                simp only [htag1, htag2, htag3, htag4, htag5, htag6, Bool.false_eq_true, ↓reduceIte]
                cases h1 : s.forallTy[e.index.toNat]? <;> rw [h1] at hr
                · simp at hr
                cases h2 : s.forallBody[e.index.toNat]? <;> rw [h2] at hr
                · simp at hr
                dsimp only at hr
                simp only [Option.some.injEq] at hr
                rw [hex.forallTy _ _ h1, hex.forallBody _ _ h2, ← hr]
              · split at hr
                · next htag1 htag2 htag3 htag4 htag5 htag6 htag7 =>
                  simp only [htag1, htag2, htag3, htag4, htag5, htag6, htag7,
                    Bool.false_eq_true, ↓reduceIte]
                  cases h1 : s.letTy[e.index.toNat]? <;> rw [h1] at hr
                  · simp at hr
                  cases h2 : s.letVal[e.index.toNat]? <;> rw [h2] at hr
                  · simp at hr
                  cases h3 : s.letBody[e.index.toNat]? <;> rw [h3] at hr
                  · simp at hr
                  dsimp only at hr
                  simp only [Option.some.injEq] at hr
                  rw [hex.letTy _ _ h1, hex.letVal _ _ h2, hex.letBody _ _ h3, ← hr]
                · cases hr

theorem lookupNode_pers_invariant (pers scr scr' : SoATier) (e : EIdx)
    (hp : e.isPers = true) :
    Arena.lookupNode pers scr' e = Arena.lookupNode pers scr e := by
  simp [Arena.lookupNode, hp]

theorem lookupNode_extends {pers scr scr' : SoATier} (hex : TierExtends scr scr')
    {e : EIdx} {c : ExprCell} (hl : Arena.lookupNode pers scr e = some c) :
    Arena.lookupNode pers scr' e = some c := by
  unfold Arena.lookupNode at hl ⊢
  split at hl
  · next hp => simpa [hp] using hl
  · next hp =>
    simp only [hp, Bool.false_eq_true, ↓reduceIte]
    exact tierRead_extends hex hl

/-- General multi-step preservation: any previously interpretable `PersTier` or
    `ScratchTier` `EIdx` retains the exact same AST interpretation under any
    extension of `ScratchTier`. -/
theorem decodeExpr_extends {pers scr scr' : SoATier} (hex : TierExtends scr scr') :
    ∀ (fuel : Nat) (e : EIdx) (ke : KExpr),
      decodeExpr pers scr fuel e = some ke ->
      decodeExpr pers scr' fuel e = some ke
  | 0, _, _, h => by simp [decodeExpr] at h
  | fuel + 1, e, ke, h => by
    simp only [decodeExpr] at h ⊢
    cases hc : Arena.lookupNode pers scr e with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      rw [lookupNode_extends hex hc]
      cases c with
      | bvar idx => exact h
      | fvar id => exact h
      | sort lvl => exact h
      | const cid => exact h
      | app fn arg =>
        dsimp only at h ⊢
        cases hfn : decodeExpr pers scr fuel fn <;> rw [hfn] at h
        · cases h
        cases harg : decodeExpr pers scr fuel arg <;> rw [harg] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_extends hex fuel fn _ hfn, decodeExpr_extends hex fuel arg _ harg]
        exact h
      | lam ty body =>
        dsimp only at h ⊢
        cases hty : decodeExpr pers scr fuel ty <;> rw [hty] at h
        · cases h
        cases hb : decodeExpr pers scr fuel body <;> rw [hb] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_extends hex fuel ty _ hty, decodeExpr_extends hex fuel body _ hb]
        exact h
      | forallE ty body =>
        dsimp only at h ⊢
        cases hty : decodeExpr pers scr fuel ty <;> rw [hty] at h
        · cases h
        cases hb : decodeExpr pers scr fuel body <;> rw [hb] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_extends hex fuel ty _ hty, decodeExpr_extends hex fuel body _ hb]
        exact h
      | letE ty val body =>
        dsimp only at h ⊢
        cases hty : decodeExpr pers scr fuel ty <;> rw [hty] at h
        · cases h
        cases hv : decodeExpr pers scr fuel val <;> rw [hv] at h
        · cases h
        cases hb : decodeExpr pers scr fuel body <;> rw [hb] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_extends hex fuel ty _ hty, decodeExpr_extends hex fuel val _ hv,
            decodeExpr_extends hex fuel body _ hb]
        exact h

/-- `decodeExpr` is monotone in fuel. -/
theorem decodeExpr_mono (pers scr : SoATier) :
    ∀ {f₁ f₂ : Nat} (_ : f₁ ≤ f₂) (e : EIdx) (ke : KExpr),
      decodeExpr pers scr f₁ e = some ke ->
      decodeExpr pers scr f₂ e = some ke
  | 0, _, _, _, _, h => by simp [decodeExpr] at h
  | _ + 1, 0, hle, _, _, _ => by omega
  | f₁ + 1, f₂ + 1, hle, e, ke, h => by
    have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
    simp only [decodeExpr] at h ⊢
    cases hc : Arena.lookupNode pers scr e with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | bvar idx => exact h
      | fvar id => exact h
      | sort lvl => exact h
      | const cid => exact h
      | app fn arg =>
        dsimp only at h ⊢
        cases hfn : decodeExpr pers scr f₁ fn <;> rw [hfn] at h
        · cases h
        cases harg : decodeExpr pers scr f₁ arg <;> rw [harg] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_mono pers scr hle' fn _ hfn, decodeExpr_mono pers scr hle' arg _ harg]
        exact h
      | lam ty body =>
        dsimp only at h ⊢
        cases hty : decodeExpr pers scr f₁ ty <;> rw [hty] at h
        · cases h
        cases hb : decodeExpr pers scr f₁ body <;> rw [hb] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_mono pers scr hle' ty _ hty, decodeExpr_mono pers scr hle' body _ hb]
        exact h
      | forallE ty body =>
        dsimp only at h ⊢
        cases hty : decodeExpr pers scr f₁ ty <;> rw [hty] at h
        · cases h
        cases hb : decodeExpr pers scr f₁ body <;> rw [hb] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_mono pers scr hle' ty _ hty, decodeExpr_mono pers scr hle' body _ hb]
        exact h
      | letE ty val body =>
        dsimp only at h ⊢
        cases hty : decodeExpr pers scr f₁ ty <;> rw [hty] at h
        · cases h
        cases hv : decodeExpr pers scr f₁ val <;> rw [hv] at h
        · cases h
        cases hb : decodeExpr pers scr f₁ body <;> rw [hb] at h
        · cases h
        dsimp only at h
        rw [decodeExpr_mono pers scr hle' ty _ hty, decodeExpr_mono pers scr hle' val _ hv,
            decodeExpr_mono pers scr hle' body _ hb]
        exact h

theorem decodeExpr_deterministic (pers scr : SoATier) {f₁ f₂ : Nat} {e : EIdx}
    {k₁ k₂ : KExpr}
    (h1 : decodeExpr pers scr f₁ e = some k₁)
    (h2 : decodeExpr pers scr f₂ e = some k₂) : k₁ = k₂ := by
  have h1' := decodeExpr_mono pers scr (Nat.le_max_left f₁ f₂) e k₁ h1
  have h2' := decodeExpr_mono pers scr (Nat.le_max_right f₁ f₂) e k₂ h2
  rw [h1'] at h2'
  exact Option.some.inj h2'

/-- Persistent-tier closure invariant: every `PersTier` node's child `EIdx`
    pointers stay within `PersTier`, ensuring complete independence from
    `ScratchTier`. -/
def PersClosed (pers : SoATier) : Prop :=
  ∀ e c, e.isPers = true -> pers.read e = some c ->
    match c with
    | .bvar _ | .fvar _ | .sort _ | .const _ => True
    | .app fn arg => fn.isPers = true ∧ arg.isPers = true
    | .lam ty b => ty.isPers = true ∧ b.isPers = true
    | .forallE ty b => ty.isPers = true ∧ b.isPers = true
    | .letE ty v b => ty.isPers = true ∧ v.isPers = true ∧ b.isPers = true

theorem decodeExpr_pers_independent (pers scr₁ scr₂ : SoATier) (hpc : PersClosed pers) :
    ∀ (fuel : Nat) (e : EIdx), e.isPers = true ->
      decodeExpr pers scr₁ fuel e = decodeExpr pers scr₂ fuel e
  | 0, _, _ => by simp [decodeExpr]
  | fuel + 1, e, hep => by
    simp only [decodeExpr, Arena.lookupNode, hep, ↓reduceIte]
    cases hc : pers.read e with
    | none => rfl
    | some c =>
      have hsub := hpc e c hep hc
      cases c with
      | bvar _ => rfl
      | fvar _ => rfl
      | sort _ => rfl
      | const _ => rfl
      | app fn arg =>
        simp only at hsub
        dsimp only
        rw [decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel fn hsub.1,
            decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel arg hsub.2]
      | lam ty b =>
        simp only at hsub
        dsimp only
        rw [decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel ty hsub.1,
            decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel b hsub.2]
      | forallE ty b =>
        simp only at hsub
        dsimp only
        rw [decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel ty hsub.1,
            decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel b hsub.2]
      | letE ty v b =>
        simp only at hsub
        dsimp only
        rw [decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel ty hsub.1,
            decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel v hsub.2.1,
            decodeExpr_pers_independent pers scr₁ scr₂ hpc fuel b hsub.2.2]

/-- Core `pers_lookup_invariant`: appending any cell to `ScratchTier` never alters
    the interpretation of any `PersTier` `EIdx` or any previously allocated valid
    `ScratchTier` `EIdx`. -/
theorem pers_lookup_invariant (pers scr : SoATier) (cell : ExprCell)
    (fuel : Nat) (e : EIdx) (ke : KExpr)
    (hdec : decodeExpr pers scr fuel e = some ke) :
    decodeExpr pers (scr.pushCell tierS cell).1 fuel e = some ke :=
  decodeExpr_extends (pushCell_extends scr tierS cell) fuel e ke hdec

/-- Stronger unconditional invariance for `PersClosed pers` handles under any
    scratch append (`some` or `none`). -/
theorem pers_closed_append_invariant (pers scr : SoATier) (hpc : PersClosed pers)
    (cell : ExprCell) (fuel : Nat) (e : EIdx) (hep : e.isPers = true) :
    decodeExpr pers (scr.pushCell tierS cell).1 fuel e = decodeExpr pers scr fuel e :=
  decodeExpr_pers_independent pers _ scr hpc fuel e hep

/-! ### 3. Functional Kernel Specification (`whnfFuel`, `defEqSpec`, `inferSpec`) -/

def imax (u v : Nat) : Nat :=
  if v == 0 then 0 else max u v

/-- Open bound variable `k` with `sub` (locally nameless instantiation). -/
def KExpr.inst (e : KExpr) (k : Nat) (sub : KExpr) : KExpr :=
  match e with
  | .bvar idx => if idx == k then sub else .bvar idx
  | .fvar id => .fvar id
  | .sort lvl => .sort lvl
  | .const cid => .const cid
  | .app fn arg => .app (fn.inst k sub) (arg.inst k sub)
  | .lam ty body => .lam (ty.inst k sub) (body.inst (k + 1) sub)
  | .forallE ty body => .forallE (ty.inst k sub) (body.inst (k + 1) sub)
  | .letE ty val body => .letE (ty.inst k sub) (val.inst k sub) (body.inst (k + 1) sub)

/-- Close free variable `fvarId` into bound variable `k`. -/
def KExpr.abst (e : KExpr) (k fvarId : Nat) : KExpr :=
  match e with
  | .bvar idx => .bvar idx
  | .fvar id => if id == fvarId then .bvar k else .fvar id
  | .sort lvl => .sort lvl
  | .const cid => .const cid
  | .app fn arg => .app (fn.abst k fvarId) (arg.abst k fvarId)
  | .lam ty body => .lam (ty.abst k fvarId) (body.abst (k + 1) fvarId)
  | .forallE ty body => .forallE (ty.abst k fvarId) (body.abst (k + 1) fvarId)
  | .letE ty val body => .letE (ty.abst k fvarId) (val.abst k fvarId) (body.abst (k + 1) fvarId)

/-- Kernel constant declaration: type plus optional transparent definition value. -/
structure ConstDecl where
  ty : KExpr
  val? : Option KExpr
  deriving DecidableEq, Repr, Inhabited

/-- Kernel declaration environment indexed by 32-bit constant ID. -/
abbrev KEnv := Array ConstDecl

/-- Functional Weak-Head Normal Form specification (beta + zeta + delta). -/
def whnfFuel (env : KEnv) : Nat -> KExpr -> Option KExpr
  | 0, _ => none
  | fuel + 1, e =>
    match e with
    | .const cid =>
      match env[cid]? with
      | some decl =>
        match decl.val? with
        | some body => whnfFuel env fuel body
        | none => some (.const cid)
      | none => some (.const cid)
    | .letE _ val body => whnfFuel env fuel (body.inst 0 val)
    | .app fn arg =>
      match whnfFuel env fuel fn with
      | some (.lam _ body) => whnfFuel env fuel (body.inst 0 arg)
      | some fn' => some (.app fn' arg)
      | none => none
    | other => some other

/-- Functional Definitional Equality specification (WHNF + structural + binder congruence). -/
def defEqSpec (env : KEnv) : Nat -> Nat -> KExpr -> KExpr -> Bool
  | 0, _, _, _ => false
  | fuel + 1, fid, a, b =>
    if a == b then true
    else
      match whnfFuel env fuel a, whnfFuel env fuel b with
      | some wa, some wb =>
        match wa, wb with
        | .bvar i, .bvar j => i == j
        | .fvar i, .fvar j => i == j
        | .sort u, .sort v => u == v
        | .const c₁, .const c₂ => c₁ == c₂
        | .app f₁ a₁, .app f₂ a₂ =>
          defEqSpec env fuel fid f₁ f₂ && defEqSpec env fuel fid a₁ a₂
        | .lam d₁ b₁, .lam d₂ b₂ =>
          defEqSpec env fuel fid d₁ d₂ &&
          defEqSpec env fuel (fid + 1) (b₁.inst 0 (.fvar fid)) (b₂.inst 0 (.fvar fid))
        | .forallE d₁ b₁, .forallE d₂ b₂ =>
          defEqSpec env fuel fid d₁ d₂ &&
          defEqSpec env fuel (fid + 1) (b₁.inst 0 (.fvar fid)) (b₂.inst 0 (.fvar fid))
        | _, _ => false
      | _, _ => false

/-- Functional Dependent Type Inference specification. -/
def inferSpec (env : KEnv) : Nat -> List KExpr -> KExpr -> Option KExpr
  | 0, _, _ => none
  | fuel + 1, ctx, e =>
    match e with
    | .bvar _ => none
    | .fvar id => ctx[id]?
    | .sort lvl => some (.sort (lvl + 1))
    | .const cid => (env[cid]?).map (·.ty)
    | .app fn arg =>
      match inferSpec env fuel ctx fn, inferSpec env fuel ctx arg with
      | some fty, some aty =>
        match whnfFuel env fuel fty with
        | some (.forallE dom cod) =>
          if defEqSpec env fuel ctx.length aty dom then
            some (cod.inst 0 arg)
          else none
        | _ => none
      | _, _ => none
    | .lam dom body =>
      match inferSpec env fuel ctx dom with
      | some domTy =>
        match whnfFuel env fuel domTy with
        | some (.sort _) =>
          let fid := ctx.length
          match inferSpec env fuel (ctx ++ [dom]) (body.inst 0 (.fvar fid)) with
          | some bodyTy => some (.forallE dom (bodyTy.abst 0 fid))
          | none => none
        | _ => none
      | none => none
    | .forallE dom body =>
      match inferSpec env fuel ctx dom with
      | some domTy =>
        match whnfFuel env fuel domTy with
        | some (.sort u) =>
          let fid := ctx.length
          match inferSpec env fuel (ctx ++ [dom]) (body.inst 0 (.fvar fid)) with
          | some bodyTy =>
            match whnfFuel env fuel bodyTy with
            | some (.sort v) => some (.sort (imax u v))
            | _ => none
          | none => none
        | _ => none
      | none => none
    | .letE ty val body =>
      match inferSpec env fuel ctx ty, inferSpec env fuel ctx val with
      | some tyTy, some valTy =>
        match whnfFuel env fuel tyTy with
        | some (.sort _) =>
          if defEqSpec env fuel ctx.length valTy ty then
            let fid := ctx.length
            match inferSpec env fuel (ctx ++ [ty]) (body.inst 0 (.fvar fid)) with
            | some bodyTy => some (.letE ty val (bodyTy.abst 0 fid))
            | none => none
          else none
        | _ => none
      | _, _ => none

/-! ### 4. Fuel Monotonicity & Determinism of Functional Kernel Spec -/

theorem whnfFuel_mono (env : KEnv) :
    ∀ {f₁ f₂ : Nat} (_ : f₁ ≤ f₂) (e w : KExpr),
      whnfFuel env f₁ e = some w -> whnfFuel env f₂ e = some w
  | 0, _, _, _, _, h => by simp [whnfFuel] at h
  | _ + 1, 0, hle, _, _, _ => by omega
  | f₁ + 1, f₂ + 1, hle, e, w, h => by
    have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
    cases e with
    | bvar idx => simpa [whnfFuel] using h
    | fvar id => simpa [whnfFuel] using h
    | sort lvl => simpa [whnfFuel] using h
    | lam ty b => simpa [whnfFuel] using h
    | forallE ty b => simpa [whnfFuel] using h
    | const cid =>
      simp only [whnfFuel] at h ⊢
      cases hd : env[cid]? with
      | none => rw [hd] at h; exact h
      | some decl =>
        rw [hd] at h
        dsimp only at h ⊢
        cases hv : decl.val? with
        | none => rw [hv] at h; exact h
        | some body =>
          rw [hv] at h
          dsimp only at h ⊢
          exact whnfFuel_mono env hle' body w h
    | letE ty val body =>
      simp only [whnfFuel] at h ⊢
      exact whnfFuel_mono env hle' (body.inst 0 val) w h
    | app fn arg =>
      simp only [whnfFuel] at h ⊢
      cases hfn : whnfFuel env f₁ fn with
      | none => rw [hfn] at h; cases h
      | some fn' =>
        rw [hfn] at h
        rw [whnfFuel_mono env hle' fn fn' hfn]
        cases fn' with
        | lam ty body =>
          exact whnfFuel_mono env hle' (body.inst 0 arg) w h
        | bvar _ | fvar _ | sort _ | const _ | app _ _ | forallE _ _ | letE _ _ _ =>
          exact h

theorem defEqSpec_mono (env : KEnv) :
    ∀ {f₁ f₂ : Nat} (_ : f₁ ≤ f₂) (fid : Nat) (a b : KExpr),
      defEqSpec env f₁ fid a b = true -> defEqSpec env f₂ fid a b = true
  | 0, _, _, _, _, _, h => by simp [defEqSpec] at h
  | _ + 1, 0, hle, _, _, _, _ => by omega
  | f₁ + 1, f₂ + 1, hle, fid, a, b, h => by
    have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
    simp only [defEqSpec] at h ⊢
    by_cases heq : (a == b) = true
    · simp [heq]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hwa : whnfFuel env f₁ a with
      | none => rw [hwa] at h; cases h
      | some wa =>
        cases hwb : whnfFuel env f₁ b with
        | none => rw [hwa, hwb] at h; cases h
        | some wb =>
          rw [hwa, hwb] at h
          rw [whnfFuel_mono env hle' a wa hwa, whnfFuel_mono env hle' b wb hwb]
          dsimp only at h ⊢
          cases wa <;> cases wb <;> simp only at h ⊢
          all_goals try exact h
          · simp only [Bool.and_eq_true] at h ⊢
            exact ⟨defEqSpec_mono env hle' fid _ _ h.1, defEqSpec_mono env hle' fid _ _ h.2⟩
          · simp only [Bool.and_eq_true] at h ⊢
            exact ⟨defEqSpec_mono env hle' fid _ _ h.1,
                   defEqSpec_mono env hle' (fid + 1) _ _ h.2⟩
          · simp only [Bool.and_eq_true] at h ⊢
            exact ⟨defEqSpec_mono env hle' fid _ _ h.1,
                   defEqSpec_mono env hle' (fid + 1) _ _ h.2⟩

theorem inferSpec_mono (env : KEnv) :
    ∀ {f₁ f₂ : Nat} (_ : f₁ ≤ f₂) (ctx : List KExpr) (e ty : KExpr),
      inferSpec env f₁ ctx e = some ty -> inferSpec env f₂ ctx e = some ty
  | 0, _, _, _, _, _, h => by simp [inferSpec] at h
  | _ + 1, 0, hle, _, _, _, _ => by omega
  | f₁ + 1, f₂ + 1, hle, ctx, e, ty, h => by
    have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
    cases e with
    | bvar _ => simp [inferSpec] at h
    | fvar id => simpa [inferSpec] using h
    | sort lvl => simpa [inferSpec] using h
    | const cid => simpa [inferSpec] using h
    | app fn arg =>
      simp only [inferSpec] at h ⊢
      cases hf : inferSpec env f₁ ctx fn with
      | none => rw [hf] at h; cases h
      | some fty =>
        rw [hf] at h
        cases ha : inferSpec env f₁ ctx arg with
        | none => rw [ha] at h; cases h
        | some aty =>
          rw [ha] at h
          rw [inferSpec_mono env hle' ctx fn fty hf, inferSpec_mono env hle' ctx arg aty ha]
          dsimp only at h ⊢
          cases hw : whnfFuel env f₁ fty with
          | none => rw [hw] at h; cases h
          | some w =>
            rw [hw] at h
            rw [whnfFuel_mono env hle' fty w hw]
            cases w with
            | forallE dom cod =>
              dsimp only at h ⊢
              split at h
              · next hde =>
                rw [defEqSpec_mono env hle' ctx.length aty dom hde]
                exact h
              · cases h
            | bvar _ | fvar _ | sort _ | const _ | app _ _ | lam _ _ | letE _ _ _ => cases h
    | lam dom body =>
      simp only [inferSpec] at h ⊢
      cases hd : inferSpec env f₁ ctx dom with
      | none => rw [hd] at h; cases h
      | some domTy =>
        rw [hd] at h
        rw [inferSpec_mono env hle' ctx dom domTy hd]
        dsimp only at h ⊢
        cases hw : whnfFuel env f₁ domTy with
        | none => rw [hw] at h; cases h
        | some w =>
          rw [hw] at h
          rw [whnfFuel_mono env hle' domTy w hw]
          cases w with
          | sort u =>
            dsimp only at h ⊢
            cases hb : inferSpec env f₁ (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) with
            | none => rw [hb] at h; cases h
            | some bty =>
              rw [hb] at h
              rw [inferSpec_mono env hle' (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) bty hb]
              exact h
          | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h
    | forallE dom body =>
      simp only [inferSpec] at h ⊢
      cases hd : inferSpec env f₁ ctx dom with
      | none => rw [hd] at h; cases h
      | some domTy =>
        rw [hd] at h
        rw [inferSpec_mono env hle' ctx dom domTy hd]
        dsimp only at h ⊢
        cases hw : whnfFuel env f₁ domTy with
        | none => rw [hw] at h; cases h
        | some w =>
          rw [hw] at h
          rw [whnfFuel_mono env hle' domTy w hw]
          cases w with
          | sort u =>
            dsimp only at h ⊢
            cases hb : inferSpec env f₁ (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) with
            | none => rw [hb] at h; cases h
            | some bty =>
              rw [hb] at h
              rw [inferSpec_mono env hle' (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) bty hb]
              dsimp only at h ⊢
              cases hwb : whnfFuel env f₁ bty with
              | none => rw [hwb] at h; cases h
              | some wb =>
                rw [hwb] at h
                rw [whnfFuel_mono env hle' bty wb hwb]
                exact h
          | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h
    | letE tyExpr val body =>
      simp only [inferSpec] at h ⊢
      cases ht : inferSpec env f₁ ctx tyExpr with
      | none => rw [ht] at h; cases h
      | some tyTy =>
        rw [ht] at h
        cases hv : inferSpec env f₁ ctx val with
        | none => rw [hv] at h; cases h
        | some valTy =>
          rw [hv] at h
          rw [inferSpec_mono env hle' ctx tyExpr tyTy ht,
              inferSpec_mono env hle' ctx val valTy hv]
          dsimp only at h ⊢
          cases hw : whnfFuel env f₁ tyTy with
          | none => rw [hw] at h; cases h
          | some w =>
            rw [hw] at h
            rw [whnfFuel_mono env hle' tyTy w hw]
            cases w with
            | sort u =>
              dsimp only at h ⊢
              split at h
              · next hde =>
                rw [defEqSpec_mono env hle' ctx.length valTy tyExpr hde]
                cases hb : inferSpec env f₁ (ctx ++ [tyExpr]) (body.inst 0 (.fvar ctx.length)) with
                | none => rw [hb] at h; cases h
                | some bty =>
                  rw [hb] at h
                  rw [inferSpec_mono env hle' (ctx ++ [tyExpr])
                        (body.inst 0 (.fvar ctx.length)) bty hb]
                  exact h
              · cases h
            | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h

/-- Declarative relational typing judgment (soundness link from `inferSpec`). -/
inductive HasType (env : KEnv) : List KExpr -> KExpr -> KExpr -> Prop
  | fvar {ctx id ty} : ctx[id]? = some ty -> HasType env ctx (.fvar id) ty
  | sort {ctx lvl} : HasType env ctx (.sort lvl) (.sort (lvl + 1))
  | const {ctx cid d} : env[cid]? = some d -> HasType env ctx (.const cid) d.ty
  | app {ctx f a fty aty dom cod f₁ f₂} :
      HasType env ctx f fty ->
      HasType env ctx a aty ->
      whnfFuel env f₁ fty = some (.forallE dom cod) ->
      defEqSpec env f₂ ctx.length aty dom = true ->
      HasType env ctx (.app f a) (cod.inst 0 a)
  | lam {ctx dom body domTy u bodyTy f₁} :
      HasType env ctx dom domTy ->
      whnfFuel env f₁ domTy = some (.sort u) ->
      HasType env (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) bodyTy ->
      HasType env ctx (.lam dom body) (.forallE dom (bodyTy.abst 0 ctx.length))
  | forallE {ctx dom body domTy bodyTy u v f₁ f₂} :
      HasType env ctx dom domTy ->
      whnfFuel env f₁ domTy = some (.sort u) ->
      HasType env (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) bodyTy ->
      whnfFuel env f₂ bodyTy = some (.sort v) ->
      HasType env ctx (.forallE dom body) (.sort (imax u v))
  | letE {ctx ty val body tyTy valTy bodyTy u f₁ f₂} :
      HasType env ctx ty tyTy ->
      HasType env ctx val valTy ->
      whnfFuel env f₁ tyTy = some (.sort u) ->
      defEqSpec env f₂ ctx.length valTy ty = true ->
      HasType env (ctx ++ [ty]) (body.inst 0 (.fvar ctx.length)) bodyTy ->
      HasType env ctx (.letE ty val body) (.letE ty val (bodyTy.abst 0 ctx.length))

theorem inferSpec_hasType (env : KEnv) :
    ∀ (fuel : Nat) (ctx : List KExpr) (e ty : KExpr),
      inferSpec env fuel ctx e = some ty -> HasType env ctx e ty
  | 0, _, _, _, h => by simp [inferSpec] at h
  | fuel + 1, ctx, e, ty, h => by
    cases e with
    | bvar _ => simp [inferSpec] at h
    | fvar id =>
      simp only [inferSpec] at h
      exact HasType.fvar h
    | sort lvl =>
      simp only [inferSpec, Option.some.injEq] at h
      rw [← h]
      exact HasType.sort
    | const cid =>
      simp only [inferSpec] at h
      cases hd : env[cid]? with
      | none => rw [hd] at h; simp at h
      | some d =>
        rw [hd] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [← h]
        exact HasType.const hd
    | app fn arg =>
      simp only [inferSpec] at h
      cases hf : inferSpec env fuel ctx fn with
      | none => rw [hf] at h; cases h
      | some fty =>
        rw [hf] at h
        cases ha : inferSpec env fuel ctx arg with
        | none => rw [ha] at h; cases h
        | some aty =>
          rw [ha] at h
          dsimp only at h
          cases hw : whnfFuel env fuel fty with
          | none => rw [hw] at h; cases h
          | some w =>
            rw [hw] at h
            cases w with
            | forallE dom cod =>
              dsimp only at h
              split at h
              · next hde =>
                simp only [Option.some.injEq] at h
                rw [← h]
                exact HasType.app (inferSpec_hasType env fuel ctx fn fty hf)
                  (inferSpec_hasType env fuel ctx arg aty ha) hw hde
              · cases h
            | bvar _ | fvar _ | sort _ | const _ | app _ _ | lam _ _ | letE _ _ _ => cases h
    | lam dom body =>
      simp only [inferSpec] at h
      cases hd : inferSpec env fuel ctx dom with
      | none => rw [hd] at h; cases h
      | some domTy =>
        rw [hd] at h
        dsimp only at h
        cases hw : whnfFuel env fuel domTy with
        | none => rw [hw] at h; cases h
        | some w =>
          rw [hw] at h
          cases w with
          | sort u =>
            dsimp only at h
            cases hb : inferSpec env fuel (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) with
            | none => rw [hb] at h; cases h
            | some bty =>
              rw [hb] at h
              simp only [Option.some.injEq] at h
              rw [← h]
              exact HasType.lam (inferSpec_hasType env fuel ctx dom domTy hd) hw
                (inferSpec_hasType env fuel _ _ _ hb)
          | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h
    | forallE dom body =>
      simp only [inferSpec] at h
      cases hd : inferSpec env fuel ctx dom with
      | none => rw [hd] at h; cases h
      | some domTy =>
        rw [hd] at h
        dsimp only at h
        cases hw : whnfFuel env fuel domTy with
        | none => rw [hw] at h; cases h
        | some w =>
          rw [hw] at h
          cases w with
          | sort u =>
            dsimp only at h
            cases hb : inferSpec env fuel (ctx ++ [dom]) (body.inst 0 (.fvar ctx.length)) with
            | none => rw [hb] at h; cases h
            | some bty =>
              rw [hb] at h
              dsimp only at h
              cases hwb : whnfFuel env fuel bty with
              | none => rw [hwb] at h; cases h
              | some wb =>
                rw [hwb] at h
                cases wb with
                | sort v =>
                  simp only [Option.some.injEq] at h
                  rw [← h]
                  exact HasType.forallE (inferSpec_hasType env fuel ctx dom domTy hd) hw
                    (inferSpec_hasType env fuel _ _ _ hb) hwb
                | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ =>
                  cases h
          | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h
    | letE tyExpr val body =>
      simp only [inferSpec] at h
      cases ht : inferSpec env fuel ctx tyExpr with
      | none => rw [ht] at h; cases h
      | some tyTy =>
        rw [ht] at h
        cases hv : inferSpec env fuel ctx val with
        | none => rw [hv] at h; cases h
        | some valTy =>
          rw [hv] at h
          dsimp only at h
          cases hw : whnfFuel env fuel tyTy with
          | none => rw [hw] at h; cases h
          | some w =>
            rw [hw] at h
            cases w with
            | sort u =>
              dsimp only at h
              split at h
              · next hde =>
                cases hb : inferSpec env fuel (ctx ++ [tyExpr]) (body.inst 0 (.fvar ctx.length)) with
                | none => rw [hb] at h; cases h
                | some bty =>
                  rw [hb] at h
                  simp only [Option.some.injEq] at h
                  rw [← h]
                  exact HasType.letE (inferSpec_hasType env fuel ctx tyExpr tyTy ht)
                    (inferSpec_hasType env fuel ctx val valTy hv) hw hde
                    (inferSpec_hasType env fuel _ _ _ hb)
              · cases h
            | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ => cases h

end ConGpuProof
