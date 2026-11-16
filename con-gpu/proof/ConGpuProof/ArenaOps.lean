/-
ConGpuProof.ArenaOps
====================
Column well-formedness, bit-packed scratch bump allocation (`allocScr`), and
bounded AST instantiation/abstraction (`scratchInst`, `scratchAbst`) preserving
the `ArenaSpec.pers_lookup_invariant` interpretation invariant.
-/

import ConGpuProof.ArenaSpec

namespace ConGpuProof

/-! ### 1. Status / Error / Resource-Delegation Types -/

structure MachineLimits where
  maxSteps : Nat := 65536
  maxFrames : Nat := 256
  maxScratch : Nat := 1536
  deriving DecidableEq, Repr, Inhabited

inductive DelegateReason where
  | stackExhausted
  | scratchExhausted
  | stepExhausted
  | intOverflow
  deriving DecidableEq, Repr, Inhabited

inductive ErrCode where
  | unboundBVar
  | unboundFVar
  | unknownConst
  | expectedPi
  | expectedSort
  | appTypeMismatch
  | letTypeMismatch
  | danglingHandle
  deriving DecidableEq, Repr, Inhabited

inductive MachineStatus (α : Type) where
  | running
  | ok (val : α)
  | err (code : ErrCode)
  | delegate (reason : DelegateReason)
  deriving DecidableEq, Repr, Inhabited

/-- Outcome of a bounded `ScratchTier` bump operation. -/
inductive ScrOp (α : Type) where
  | ok (scr : SoATier) (val : α)
  | err (code : ErrCode)
  | delegate (reason : DelegateReason)
  deriving Repr, Inhabited

/-- GPU read-only constant entry referencing `PersTier` expression handles. -/
structure GpuConstDecl where
  ty : EIdx
  val? : Option EIdx
  deriving DecidableEq, Repr, Inhabited

/-- Soundness correspondence between GPU `PersTier` constant table and `KEnv`. -/
def EnvSound (pers : SoATier) (gpuEnv : Array GpuConstDecl) (env : KEnv) : Prop :=
  ∀ cid : Nat,
    match gpuEnv[cid]?, env[cid]? with
    | none, none => True
    | some gd, some kd =>
      (∃ ft, decodeExpr pers SoATier.empty ft gd.ty = some kd.ty) ∧
      match gd.val?, kd.val? with
      | none, none => True
      | some gv, some kv => ∃ fv, decodeExpr pers SoATier.empty fv gv = some kv
      | _, _ => False
    | _, _ => False

/-! ### 2. `SoATier` Column Invariants & Bump-Allocation Roundtrip -/

structure ScratchColsWF (s : SoATier) : Prop where
  appLen : s.appFn.size = s.appArg.size
  lamLen : s.lamTy.size = s.lamBody.size
  forallLen : s.forallTy.size = s.forallBody.size
  letLen1 : s.letTy.size = s.letVal.size
  letLen2 : s.letVal.size = s.letBody.size

theorem scratchColsWF_empty : ScratchColsWF SoATier.empty :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem scratchColsWF_pushCell {s : SoATier} (wf : ScratchColsWF s)
    (tier : UInt32) (c : ExprCell) :
    ScratchColsWF (s.pushCell tier c).1 := by
  cases c with
  | bvar _ | fvar _ | sort _ | const _ =>
    exact ⟨wf.appLen, wf.lamLen, wf.forallLen, wf.letLen1, wf.letLen2⟩
  | app _ _ =>
    exact ⟨by simp [SoATier.pushCell, SoATier.pushApp, Array.size_push, wf.appLen],
           wf.lamLen, wf.forallLen, wf.letLen1, wf.letLen2⟩
  | lam _ _ =>
    exact ⟨wf.appLen,
           by simp [SoATier.pushCell, SoATier.pushLam, Array.size_push, wf.lamLen],
           wf.forallLen, wf.letLen1, wf.letLen2⟩
  | forallE _ _ =>
    exact ⟨wf.appLen, wf.lamLen,
           by simp [SoATier.pushCell, SoATier.pushForall, Array.size_push, wf.forallLen],
           wf.letLen1, wf.letLen2⟩
  | letE _ _ _ =>
    exact ⟨wf.appLen, wf.lamLen, wf.forallLen,
           by simp [SoATier.pushCell, SoATier.pushLet, Array.size_push, wf.letLen1],
           by simp [SoATier.pushCell, SoATier.pushLet, Array.size_push, wf.letLen2]⟩

theorem tierExtends_empty (scr : SoATier) : TierExtends SoATier.empty scr := by
  have hempty : ∀ {α : Type} (b : Array α), ArrayExtends (#[] : Array α) b := by
    intro α b i v h
    have hnone : (#[] : Array α)[i]? = none := by simp
    rw [hnone] at h
    cases h
  exact ⟨hempty _, hempty _, hempty _, hempty _, hempty _, hempty _,
         hempty _, hempty _, hempty _, hempty _, hempty _, hempty _, hempty _⟩

private theorem u32_ofNat_lt_idxCap {n : Nat} (hn : n < idxCap.toNat) :
    UInt32.ofNat n < idxCap := by
  change (UInt32.ofNat n).toNat < idxCap.toNat
  have h1 : idxCap.toNat = 67108864 := rfl
  have h2 : (UInt32.ofNat n).toNat = n % 4294967296 := rfl
  omega

private theorem u32_ofNat_lt_wideCap {n : Nat} (hn : n < idxCap.toNat) :
    UInt32.ofNat n < wideCap := by
  change (UInt32.ofNat n).toNat < wideCap.toNat
  have h1 : idxCap.toNat = 67108864 := rfl
  have h2 : wideCap.toNat = 1073741824 := rfl
  have h3 : (UInt32.ofNat n).toNat = n % 4294967296 := rfl
  omega

private theorem u32_ofNat_toNat_lt_idxCap {n : Nat} (hn : n < idxCap.toNat) :
    (UInt32.ofNat n).toNat = n := by
  have h1 : idxCap.toNat = 67108864 := rfl
  change n % 4294967296 = n
  omega

private theorem tierS_lt_2 : tierS < 2 := by decide
private theorem etag_lt_16_bvar : etagBVar < 16 := by decide
private theorem etag_lt_16_fvar : etagFVar < 16 := by decide
private theorem etag_lt_16_sort : etagSort < 16 := by decide
private theorem etag_lt_16_const : etagConst < 16 := by decide
private theorem etag_lt_16_lam : etagLam < 16 := by decide
private theorem etag_lt_16_forall : etagForall < 16 := by decide
private theorem etag_lt_16_let : etagLet < 16 := by decide

private theorem array_push_getElem?_size {α : Type} (xs : Array α) (v : α) :
    (xs.push v)[xs.size]? = some v := by
  have hsz : xs.size < (xs.push v).size := by rw [Array.size_push]; omega
  rw [Array.getElem?_eq_getElem hsz, Array.getElem_push_eq]

private theorem isPers_pack_tierS {tg idx : UInt32}
    (hg : tg < 16) (hi : idx < idxCap) :
    (EIdx.pack tg tierS idx).isPers = false := by
  unfold EIdx.isPers
  rw [EIdx.tier_pack tierS_lt_2 hg hi]
  decide

private theorem isPers_packWide_tierS {idx : UInt32}
    (hi : idx < wideCap) :
    (EIdx.packWide tierS idx).isPers = false := by
  unfold EIdx.isPers
  rw [EIdx.tier_packWide tierS_lt_2 hi]
  decide

theorem lookupNode_pushCell (pers scr : SoATier) (wf : ScratchColsWF scr)
    (hcap : scr.totalNodes < idxCap.toNat) (cell : ExprCell) :
    Arena.lookupNode pers (scr.pushCell tierS cell).1 (scr.pushCell tierS cell).2 = some cell := by
  have hb : scr.bvars.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  have hf : scr.fvars.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  have hs : scr.sorts.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  have hc : scr.consts.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  have ha : scr.appFn.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  have hl : scr.lamTy.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  have hp : scr.forallTy.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  have hz : scr.letTy.size < idxCap.toNat := by unfold SoATier.totalNodes at hcap; omega
  cases cell with
  | bvar v =>
    have hi := u32_ofNat_lt_idxCap hb
    have hidx := u32_ofNat_toNat_lt_idxCap hb
    simp only [SoATier.pushCell, SoATier.pushBVar, Arena.lookupNode,
      isPers_pack_tierS etag_lt_16_bvar hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_pack tierS_lt_2 etag_lt_16_bvar hi,
      EIdx.tag_pack tierS_lt_2 etag_lt_16_bvar hi,
      EIdx.index_pack tierS_lt_2 etag_lt_16_bvar hi, hidx]
    simp only [etagBVar, beq_self_eq_true, ↓reduceIte, array_push_getElem?_size, Option.map_some]
  | fvar v =>
    have hi := u32_ofNat_lt_idxCap hf
    have hidx := u32_ofNat_toNat_lt_idxCap hf
    simp only [SoATier.pushCell, SoATier.pushFVar, Arena.lookupNode,
      isPers_pack_tierS etag_lt_16_fvar hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_pack tierS_lt_2 etag_lt_16_fvar hi,
      EIdx.tag_pack tierS_lt_2 etag_lt_16_fvar hi,
      EIdx.index_pack tierS_lt_2 etag_lt_16_fvar hi, hidx]
    simp only [etagFVar, etagBVar, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
      show ((1 : UInt32) == 0) = false by decide,
      array_push_getElem?_size, Option.map_some]
  | sort v =>
    have hi := u32_ofNat_lt_idxCap hs
    have hidx := u32_ofNat_toNat_lt_idxCap hs
    simp only [SoATier.pushCell, SoATier.pushSort, Arena.lookupNode,
      isPers_pack_tierS etag_lt_16_sort hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_pack tierS_lt_2 etag_lt_16_sort hi,
      EIdx.tag_pack tierS_lt_2 etag_lt_16_sort hi,
      EIdx.index_pack tierS_lt_2 etag_lt_16_sort hi, hidx]
    simp only [etagSort, etagBVar, etagFVar, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
      show ((2 : UInt32) == 0) = false by decide,
      show ((2 : UInt32) == 1) = false by decide,
      array_push_getElem?_size, Option.map_some]
  | const v =>
    have hi := u32_ofNat_lt_idxCap hc
    have hidx := u32_ofNat_toNat_lt_idxCap hc
    simp only [SoATier.pushCell, SoATier.pushConst, Arena.lookupNode,
      isPers_pack_tierS etag_lt_16_const hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_pack tierS_lt_2 etag_lt_16_const hi,
      EIdx.tag_pack tierS_lt_2 etag_lt_16_const hi,
      EIdx.index_pack tierS_lt_2 etag_lt_16_const hi, hidx]
    simp only [etagConst, etagBVar, etagFVar, etagSort, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
      show ((3 : UInt32) == 0) = false by decide,
      show ((3 : UInt32) == 1) = false by decide,
      show ((3 : UInt32) == 2) = false by decide,
      array_push_getElem?_size, Option.map_some]
  | app fn arg =>
    have hmin : min scr.appFn.size scr.appArg.size = scr.appFn.size := by
      have := wf.appLen; omega
    have hi := u32_ofNat_lt_wideCap ha
    have hidx := u32_ofNat_toNat_lt_idxCap ha
    simp only [SoATier.pushCell, SoATier.pushApp, hmin, Arena.lookupNode,
      isPers_packWide_tierS hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_packWide tierS_lt_2 hi,
      EIdx.index_packWide tierS_lt_2 hi, hidx]
    rw [array_push_getElem?_size, wf.appLen, array_push_getElem?_size]
  | lam ty body =>
    have hmin : min scr.lamTy.size scr.lamBody.size = scr.lamTy.size := by
      have := wf.lamLen; omega
    have hi := u32_ofNat_lt_idxCap hl
    have hidx := u32_ofNat_toNat_lt_idxCap hl
    simp only [SoATier.pushCell, SoATier.pushLam, hmin, Arena.lookupNode,
      isPers_pack_tierS etag_lt_16_lam hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_pack tierS_lt_2 etag_lt_16_lam hi,
      EIdx.tag_pack tierS_lt_2 etag_lt_16_lam hi,
      EIdx.index_pack tierS_lt_2 etag_lt_16_lam hi, hidx]
    simp only [etagLam, etagBVar, etagFVar, etagSort, etagConst,
      beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
      show ((5 : UInt32) == 0) = false by decide,
      show ((5 : UInt32) == 1) = false by decide,
      show ((5 : UInt32) == 2) = false by decide,
      show ((5 : UInt32) == 3) = false by decide]
    rw [array_push_getElem?_size, wf.lamLen, array_push_getElem?_size]
  | forallE ty body =>
    have hmin : min scr.forallTy.size scr.forallBody.size = scr.forallTy.size := by
      have := wf.forallLen; omega
    have hi := u32_ofNat_lt_idxCap hp
    have hidx := u32_ofNat_toNat_lt_idxCap hp
    simp only [SoATier.pushCell, SoATier.pushForall, hmin, Arena.lookupNode,
      isPers_pack_tierS etag_lt_16_forall hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_pack tierS_lt_2 etag_lt_16_forall hi,
      EIdx.tag_pack tierS_lt_2 etag_lt_16_forall hi,
      EIdx.index_pack tierS_lt_2 etag_lt_16_forall hi, hidx]
    simp only [etagForall, etagBVar, etagFVar, etagSort, etagConst, etagLam,
      beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
      show ((6 : UInt32) == 0) = false by decide,
      show ((6 : UInt32) == 1) = false by decide,
      show ((6 : UInt32) == 2) = false by decide,
      show ((6 : UInt32) == 3) = false by decide,
      show ((6 : UInt32) == 5) = false by decide]
    rw [array_push_getElem?_size, wf.forallLen, array_push_getElem?_size]
  | letE ty val body =>
    have hmin : min scr.letTy.size (min scr.letVal.size scr.letBody.size) = scr.letTy.size := by
      have := wf.letLen1; have := wf.letLen2; omega
    have hi := u32_ofNat_lt_idxCap hz
    have hidx := u32_ofNat_toNat_lt_idxCap hz
    simp only [SoATier.pushCell, SoATier.pushLet, hmin, Arena.lookupNode,
      isPers_pack_tierS etag_lt_16_let hi, Bool.false_eq_true, ↓reduceIte,
      SoATier.read, EIdx.isWide_pack tierS_lt_2 etag_lt_16_let hi,
      EIdx.tag_pack tierS_lt_2 etag_lt_16_let hi,
      EIdx.index_pack tierS_lt_2 etag_lt_16_let hi, hidx]
    simp only [etagLet, etagBVar, etagFVar, etagSort, etagConst, etagLam, etagForall,
      beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
      show ((7 : UInt32) == 0) = false by decide,
      show ((7 : UInt32) == 1) = false by decide,
      show ((7 : UInt32) == 2) = false by decide,
      show ((7 : UInt32) == 3) = false by decide,
      show ((7 : UInt32) == 5) = false by decide,
      show ((7 : UInt32) == 6) = false by decide]
    rw [array_push_getElem?_size, wf.letLen1, array_push_getElem?_size,
        wf.letLen2, array_push_getElem?_size]

/-! ### 3. Checked Scratch Bump Allocator (`allocScr`) -/

def allocScr (cfg : MachineLimits) (scr : SoATier) (c : ExprCell) : ScrOp EIdx :=
  if scr.totalNodes < cfg.maxScratch && scr.totalNodes < idxCap.toNat then
    let (scr', e') := scr.pushCell tierS c
    .ok scr' e'
  else
    .delegate .scratchExhausted

theorem allocScr_extends {cfg : MachineLimits} {scr scr' : SoATier}
    {c : ExprCell} {e' : EIdx}
    (h : allocScr cfg scr c = .ok scr' e') :
    TierExtends scr scr' := by
  unfold allocScr at h
  split at h
  · dsimp only at h
    simp only [ScrOp.ok.injEq] at h
    rcases h with ⟨rfl, _⟩
    exact pushCell_extends scr tierS c
  · cases h

theorem allocScr_wf (pers : SoATier) {cfg : MachineLimits} {scr scr' : SoATier}
    {c : ExprCell} {e' : EIdx}
    (wf : ScratchColsWF scr) (h : allocScr cfg scr c = .ok scr' e') :
    ScratchColsWF scr' ∧ Arena.lookupNode pers scr' e' = some c := by
  unfold allocScr at h
  split at h
  · next hcond =>
    rw [Bool.and_eq_true] at hcond
    have hcap : scr.totalNodes < idxCap.toNat := decide_eq_true_eq.mp hcond.2
    dsimp only at h
    simp only [ScrOp.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨scratchColsWF_pushCell wf tierS c, lookupNode_pushCell pers scr wf hcap c⟩
  · cases h

/-! ### 4. Bounded Scratch AST Instantiation & Abstraction -/

def scratchInst (cfg : MachineLimits) (pers scr : SoATier) :
    Nat -> Nat -> EIdx -> EIdx -> ScrOp EIdx
  | 0, _, _, _ => .delegate .scratchExhausted
  | fuel + 1, k, sub, e =>
    match Arena.lookupNode pers scr e with
    | none => .err .danglingHandle
    | some (.bvar idx) =>
      if idx.toNat == k then .ok scr sub else .ok scr e
    | some (.fvar _) | some (.sort _) | some (.const _) => .ok scr e
    | some (.app fn arg) =>
      match scratchInst cfg pers scr fuel k sub fn with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ fn' =>
        match scratchInst cfg pers scr₁ fuel k sub arg with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ arg' => allocScr cfg scr₂ (.app fn' arg')
    | some (.lam ty body) =>
      match scratchInst cfg pers scr fuel k sub ty with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ ty' =>
        match scratchInst cfg pers scr₁ fuel (k + 1) sub body with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ body' => allocScr cfg scr₂ (.lam ty' body')
    | some (.forallE ty body) =>
      match scratchInst cfg pers scr fuel k sub ty with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ ty' =>
        match scratchInst cfg pers scr₁ fuel (k + 1) sub body with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ body' => allocScr cfg scr₂ (.forallE ty' body')
    | some (.letE ty val body) =>
      match scratchInst cfg pers scr fuel k sub ty with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ ty' =>
        match scratchInst cfg pers scr₁ fuel k sub val with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ val' =>
          match scratchInst cfg pers scr₂ fuel (k + 1) sub body with
          | .err c => .err c
          | .delegate r => .delegate r
          | .ok scr₃ body' => allocScr cfg scr₃ (.letE ty' val' body')

def scratchAbst (cfg : MachineLimits) (pers scr : SoATier) :
    Nat -> Nat -> Nat -> EIdx -> ScrOp EIdx
  | 0, _, _, _ => .delegate .scratchExhausted
  | fuel + 1, k, fvarId, e =>
    match Arena.lookupNode pers scr e with
    | none => .err .danglingHandle
    | some (.bvar _) | some (.sort _) | some (.const _) => .ok scr e
    | some (.fvar id) =>
      if id.toNat == fvarId then
        if k < 4294967296 then
          allocScr cfg scr (.bvar (UInt32.ofNat k))
        else
          .delegate .intOverflow
      else
        .ok scr e
    | some (.app fn arg) =>
      match scratchAbst cfg pers scr fuel k fvarId fn with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ fn' =>
        match scratchAbst cfg pers scr₁ fuel k fvarId arg with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ arg' => allocScr cfg scr₂ (.app fn' arg')
    | some (.lam ty body) =>
      match scratchAbst cfg pers scr fuel k fvarId ty with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ ty' =>
        match scratchAbst cfg pers scr₁ fuel (k + 1) fvarId body with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ body' => allocScr cfg scr₂ (.lam ty' body')
    | some (.forallE ty body) =>
      match scratchAbst cfg pers scr fuel k fvarId ty with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ ty' =>
        match scratchAbst cfg pers scr₁ fuel (k + 1) fvarId body with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ body' => allocScr cfg scr₂ (.forallE ty' body')
    | some (.letE ty val body) =>
      match scratchAbst cfg pers scr fuel k fvarId ty with
      | .err c => .err c
      | .delegate r => .delegate r
      | .ok scr₁ ty' =>
        match scratchAbst cfg pers scr₁ fuel k fvarId val with
        | .err c => .err c
        | .delegate r => .delegate r
        | .ok scr₂ val' =>
          match scratchAbst cfg pers scr₂ fuel (k + 1) fvarId body with
          | .err c => .err c
          | .delegate r => .delegate r
          | .ok scr₃ body' => allocScr cfg scr₃ (.letE ty' val' body')

/-- Semantic shorthand: handle `e` decodes to `ke` in `(pers, scr)` for some depth. -/
def Interprets (pers scr : SoATier) (e : EIdx) (ke : KExpr) : Prop :=
  ∃ f, decodeExpr pers scr f e = some ke

theorem interprets_extends {pers scr scr' : SoATier} (hex : TierExtends scr scr')
    {e : EIdx} {ke : KExpr} (hi : Interprets pers scr e ke) :
    Interprets pers scr' e ke := by
  rcases hi with ⟨f, hf⟩
  exact ⟨f, decodeExpr_extends hex f e ke hf⟩

private theorem decodeExpr_lookup_cell (pers scr : SoATier) {e : EIdx} {c : ExprCell}
    (hl : Arena.lookupNode pers scr e = some c) :
    match c with
    | .bvar idx => decodeExpr pers scr 1 e = some (.bvar idx.toNat)
    | .fvar id => decodeExpr pers scr 1 e = some (.fvar id.toNat)
    | .sort lvl => decodeExpr pers scr 1 e = some (.sort lvl.toNat)
    | .const cid => decodeExpr pers scr 1 e = some (.const cid.toNat)
    | .app fn arg =>
      ∀ {kfn karg : KExpr}, Interprets pers scr fn kfn -> Interprets pers scr arg karg ->
        Interprets pers scr e (.app kfn karg)
    | .lam ty b =>
      ∀ {kty kb : KExpr}, Interprets pers scr ty kty -> Interprets pers scr b kb ->
        Interprets pers scr e (.lam kty kb)
    | .forallE ty b =>
      ∀ {kty kb : KExpr}, Interprets pers scr ty kty -> Interprets pers scr b kb ->
        Interprets pers scr e (.forallE kty kb)
    | .letE ty v b =>
      ∀ {kty kv kb : KExpr}, Interprets pers scr ty kty -> Interprets pers scr v kv ->
        Interprets pers scr b kb -> Interprets pers scr e (.letE kty kv kb) := by
  cases c with
  | bvar idx => simp [decodeExpr, hl]
  | fvar id => simp [decodeExpr, hl]
  | sort lvl => simp [decodeExpr, hl]
  | const cid => simp [decodeExpr, hl]
  | app fn arg =>
    intro kfn karg ⟨f1, h1⟩ ⟨f2, h2⟩
    refine ⟨max f1 f2 + 1, ?_⟩
    have h1' := decodeExpr_mono pers scr (Nat.le_max_left f1 f2) fn kfn h1
    have h2' := decodeExpr_mono pers scr (Nat.le_max_right f1 f2) arg karg h2
    simp [decodeExpr, hl, h1', h2']
  | lam ty b =>
    intro kty kb ⟨f1, h1⟩ ⟨f2, h2⟩
    refine ⟨max f1 f2 + 1, ?_⟩
    have h1' := decodeExpr_mono pers scr (Nat.le_max_left f1 f2) ty kty h1
    have h2' := decodeExpr_mono pers scr (Nat.le_max_right f1 f2) b kb h2
    simp [decodeExpr, hl, h1', h2']
  | forallE ty b =>
    intro kty kb ⟨f1, h1⟩ ⟨f2, h2⟩
    refine ⟨max f1 f2 + 1, ?_⟩
    have h1' := decodeExpr_mono pers scr (Nat.le_max_left f1 f2) ty kty h1
    have h2' := decodeExpr_mono pers scr (Nat.le_max_right f1 f2) b kb h2
    simp [decodeExpr, hl, h1', h2']
  | letE ty v b =>
    intro kty kv kb ⟨f1, h1⟩ ⟨f2, h2⟩ ⟨f3, h3⟩
    refine ⟨max f1 (max f2 f3) + 1, ?_⟩
    have h1' := decodeExpr_mono pers scr (Nat.le_max_left f1 (max f2 f3)) ty kty h1
    have h2' := decodeExpr_mono pers scr
      (Nat.le_trans (Nat.le_max_left f2 f3) (Nat.le_max_right f1 (max f2 f3))) v kv h2
    have h3' := decodeExpr_mono pers scr
      (Nat.le_trans (Nat.le_max_right f2 f3) (Nat.le_max_right f1 (max f2 f3))) b kb h3
    simp [decodeExpr, hl, h1', h2', h3']

private theorem decodeExpr_invert_cell (pers scr : SoATier) :
    ∀ {f : Nat} {e : EIdx} {c : ExprCell} {ke : KExpr},
      decodeExpr pers scr f e = some ke ->
      Arena.lookupNode pers scr e = some c ->
      match c with
      | .bvar idx => ke = .bvar idx.toNat
      | .fvar id => ke = .fvar id.toNat
      | .sort lvl => ke = .sort lvl.toNat
      | .const cid => ke = .const cid.toNat
      | .app fn arg => ∃ kfn karg, ke = .app kfn karg ∧
          Interprets pers scr fn kfn ∧ Interprets pers scr arg karg
      | .lam ty b => ∃ kty kb, ke = .lam kty kb ∧
          Interprets pers scr ty kty ∧ Interprets pers scr b kb
      | .forallE ty b => ∃ kty kb, ke = .forallE kty kb ∧
          Interprets pers scr ty kty ∧ Interprets pers scr b kb
      | .letE ty v b => ∃ kty kv kb, ke = .letE kty kv kb ∧
          Interprets pers scr ty kty ∧ Interprets pers scr v kv ∧ Interprets pers scr b kb
  | 0, _, _, _, hd, _ => by simp [decodeExpr] at hd
  | f + 1, e, c, ke, hd, hl => by
    simp only [decodeExpr, hl] at hd
    cases c with
    | bvar idx => exact (Option.some.inj hd).symm
    | fvar id => exact (Option.some.inj hd).symm
    | sort lvl => exact (Option.some.inj hd).symm
    | const cid => exact (Option.some.inj hd).symm
    | app fn arg =>
      dsimp only at hd
      cases h1 : decodeExpr pers scr f fn <;> rw [h1] at hd
      · dsimp only at hd; cases hd
      cases h2 : decodeExpr pers scr f arg <;> rw [h2] at hd
      · dsimp only at hd; cases hd
      dsimp only at hd
      exact ⟨_, _, (Option.some.inj hd).symm, ⟨f, h1⟩, ⟨f, h2⟩⟩
    | lam ty b =>
      dsimp only at hd
      cases h1 : decodeExpr pers scr f ty <;> rw [h1] at hd
      · dsimp only at hd; cases hd
      cases h2 : decodeExpr pers scr f b <;> rw [h2] at hd
      · dsimp only at hd; cases hd
      dsimp only at hd
      exact ⟨_, _, (Option.some.inj hd).symm, ⟨f, h1⟩, ⟨f, h2⟩⟩
    | forallE ty b =>
      dsimp only at hd
      cases h1 : decodeExpr pers scr f ty <;> rw [h1] at hd
      · dsimp only at hd; cases hd
      cases h2 : decodeExpr pers scr f b <;> rw [h2] at hd
      · dsimp only at hd; cases hd
      dsimp only at hd
      exact ⟨_, _, (Option.some.inj hd).symm, ⟨f, h1⟩, ⟨f, h2⟩⟩
    | letE ty v b =>
      dsimp only at hd
      cases h1 : decodeExpr pers scr f ty <;> rw [h1] at hd
      · dsimp only at hd; cases hd
      cases h2 : decodeExpr pers scr f v <;> rw [h2] at hd
      · dsimp only at hd; cases hd
      cases h3 : decodeExpr pers scr f b <;> rw [h3] at hd
      · dsimp only at hd; cases hd
      dsimp only at hd
      exact ⟨_, _, _, (Option.some.inj hd).symm, ⟨f, h1⟩, ⟨f, h2⟩, ⟨f, h3⟩⟩

theorem scratchInst_extends (cfg : MachineLimits) (pers : SoATier) :
    ∀ (fuel : Nat) (scr scr' : SoATier) (k : Nat) (sub e e' : EIdx),
      ScratchColsWF scr ->
      scratchInst cfg pers scr fuel k sub e = .ok scr' e' ->
      ScratchColsWF scr' ∧ TierExtends scr scr'
  | 0, _, _, _, _, _, _, _, h => by simp [scratchInst] at h
  | fuel + 1, scr, scr', k, sub, e, e', wf, h => by
    simp only [scratchInst] at h
    cases hl : Arena.lookupNode pers scr e with
    | none => rw [hl] at h; cases h
    | some cell =>
      rw [hl] at h
      cases cell with
      | bvar idx =>
        dsimp only at h
        split at h <;> simp only [ScrOp.ok.injEq] at h <;>
          rcases h with ⟨rfl, _⟩ <;> exact ⟨wf, tierExtends_refl _⟩
      | fvar _ | sort _ | const _ =>
        dsimp only at h
        simp only [ScrOp.ok.injEq] at h
        rcases h with ⟨rfl, _⟩
        exact ⟨wf, tierExtends_refl _⟩
      | app fn arg =>
        dsimp only at h
        cases h1 : scratchInst cfg pers scr fuel k sub fn with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ fn' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub fn fn' wf h1
          cases h2 : scratchInst cfg pers scr₁ fuel k sub arg with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ arg' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ k sub arg arg' wf₁ h2
            have h3 := allocScr_wf pers wf₂ h
            exact ⟨h3.1, tierExtends_trans ex₁ (tierExtends_trans ex₂ (allocScr_extends h))⟩
      | lam ty body =>
        dsimp only at h
        cases h1 : scratchInst cfg pers scr fuel k sub ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub ty ty' wf h1
          cases h2 : scratchInst cfg pers scr₁ fuel (k + 1) sub body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ (k + 1) sub body body' wf₁ h2
            have h3 := allocScr_wf pers wf₂ h
            exact ⟨h3.1, tierExtends_trans ex₁ (tierExtends_trans ex₂ (allocScr_extends h))⟩
      | forallE ty body =>
        dsimp only at h
        cases h1 : scratchInst cfg pers scr fuel k sub ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub ty ty' wf h1
          cases h2 : scratchInst cfg pers scr₁ fuel (k + 1) sub body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ (k + 1) sub body body' wf₁ h2
            have h3 := allocScr_wf pers wf₂ h
            exact ⟨h3.1, tierExtends_trans ex₁ (tierExtends_trans ex₂ (allocScr_extends h))⟩
      | letE ty val body =>
        dsimp only at h
        cases h1 : scratchInst cfg pers scr fuel k sub ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub ty ty' wf h1
          cases h2 : scratchInst cfg pers scr₁ fuel k sub val with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ val' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ k sub val val' wf₁ h2
            cases h3 : scratchInst cfg pers scr₂ fuel (k + 1) sub body with
            | err _ | delegate _ => rw [h3] at h; cases h
            | ok scr₃ body' =>
              rw [h3] at h; dsimp only at h
              have ⟨wf₃, ex₃⟩ := scratchInst_extends cfg pers fuel scr₂ scr₃ (k + 1) sub body body' wf₂ h3
              have h4 := allocScr_wf pers wf₃ h
              exact ⟨h4.1, tierExtends_trans ex₁
                (tierExtends_trans ex₂ (tierExtends_trans ex₃ (allocScr_extends h)))⟩

theorem scratchInst_sound (cfg : MachineLimits) (pers : SoATier) :
    ∀ (fuel : Nat) (scr scr' : SoATier) (k : Nat) (sub e e' : EIdx) (ke ksub : KExpr),
      ScratchColsWF scr ->
      Interprets pers scr e ke ->
      Interprets pers scr sub ksub ->
      scratchInst cfg pers scr fuel k sub e = .ok scr' e' ->
      Interprets pers scr' e' (ke.inst k ksub)
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [scratchInst] at h
  | fuel + 1, scr, scr', k, sub, e, e', ke, ksub, wf, ⟨fe, he⟩, hsub, h => by
    simp only [scratchInst] at h
    cases hl : Arena.lookupNode pers scr e with
    | none => rw [hl] at h; cases h
    | some cell =>
      rw [hl] at h
      have hinv := decodeExpr_invert_cell pers scr he hl
      cases cell with
      | bvar idx =>
        dsimp only at h hinv
        subst hinv
        split at h
        · next heq =>
          simp only [ScrOp.ok.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simpa [KExpr.inst, heq] using hsub
        · next hne =>
          simp only [ScrOp.ok.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          refine ⟨fe, ?_⟩
          simpa [KExpr.inst, hne] using he
      | fvar _ | sort _ | const _ =>
        dsimp only at h hinv
        subst hinv
        simp only [ScrOp.ok.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨fe, by simpa [KExpr.inst] using he⟩
      | app fn arg =>
        dsimp only at h hinv
        rcases hinv with ⟨kfn, karg, rfl, hfn, harg⟩
        cases h1 : scratchInst cfg pers scr fuel k sub fn with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ fn' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub fn fn' wf h1
          have ih₁ := scratchInst_sound cfg pers fuel scr scr₁ k sub fn fn' kfn ksub wf hfn hsub h1
          cases h2 : scratchInst cfg pers scr₁ fuel k sub arg with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ arg' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ k sub arg arg' wf₁ h2
            have ih₂ := scratchInst_sound cfg pers fuel scr₁ scr₂ k sub arg arg' karg ksub wf₁
              (interprets_extends ex₁ harg) (interprets_extends ex₁ hsub) h2
            have ex₃ := allocScr_extends h
            have hw := (allocScr_wf pers wf₂ h).2
            exact decodeExpr_lookup_cell pers scr' hw
              (interprets_extends (tierExtends_trans ex₂ ex₃) ih₁)
              (interprets_extends ex₃ ih₂)
      | lam ty body =>
        dsimp only at h hinv
        rcases hinv with ⟨kty, kb, rfl, hty, hb⟩
        cases h1 : scratchInst cfg pers scr fuel k sub ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub ty ty' wf h1
          have ih₁ := scratchInst_sound cfg pers fuel scr scr₁ k sub ty ty' kty ksub wf hty hsub h1
          cases h2 : scratchInst cfg pers scr₁ fuel (k + 1) sub body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ (k + 1) sub body body' wf₁ h2
            have ih₂ := scratchInst_sound cfg pers fuel scr₁ scr₂ (k + 1) sub body body' kb ksub wf₁
              (interprets_extends ex₁ hb) (interprets_extends ex₁ hsub) h2
            have ex₃ := allocScr_extends h
            have hw := (allocScr_wf pers wf₂ h).2
            exact decodeExpr_lookup_cell pers scr' hw
              (interprets_extends (tierExtends_trans ex₂ ex₃) ih₁)
              (interprets_extends ex₃ ih₂)
      | forallE ty body =>
        dsimp only at h hinv
        rcases hinv with ⟨kty, kb, rfl, hty, hb⟩
        cases h1 : scratchInst cfg pers scr fuel k sub ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub ty ty' wf h1
          have ih₁ := scratchInst_sound cfg pers fuel scr scr₁ k sub ty ty' kty ksub wf hty hsub h1
          cases h2 : scratchInst cfg pers scr₁ fuel (k + 1) sub body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ (k + 1) sub body body' wf₁ h2
            have ih₂ := scratchInst_sound cfg pers fuel scr₁ scr₂ (k + 1) sub body body' kb ksub wf₁
              (interprets_extends ex₁ hb) (interprets_extends ex₁ hsub) h2
            have ex₃ := allocScr_extends h
            have hw := (allocScr_wf pers wf₂ h).2
            exact decodeExpr_lookup_cell pers scr' hw
              (interprets_extends (tierExtends_trans ex₂ ex₃) ih₁)
              (interprets_extends ex₃ ih₂)
      | letE ty val body =>
        dsimp only at h hinv
        rcases hinv with ⟨kty, kv, kb, rfl, hty, hv, hb⟩
        cases h1 : scratchInst cfg pers scr fuel k sub ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchInst_extends cfg pers fuel scr scr₁ k sub ty ty' wf h1
          have ih₁ := scratchInst_sound cfg pers fuel scr scr₁ k sub ty ty' kty ksub wf hty hsub h1
          cases h2 : scratchInst cfg pers scr₁ fuel k sub val with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ val' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchInst_extends cfg pers fuel scr₁ scr₂ k sub val val' wf₁ h2
            have ih₂ := scratchInst_sound cfg pers fuel scr₁ scr₂ k sub val val' kv ksub wf₁
              (interprets_extends ex₁ hv) (interprets_extends ex₁ hsub) h2
            cases h3 : scratchInst cfg pers scr₂ fuel (k + 1) sub body with
            | err _ | delegate _ => rw [h3] at h; cases h
            | ok scr₃ body' =>
              rw [h3] at h; dsimp only at h
              have ⟨wf₃, ex₃⟩ := scratchInst_extends cfg pers fuel scr₂ scr₃ (k + 1) sub body body' wf₂ h3
              have ih₃ := scratchInst_sound cfg pers fuel scr₂ scr₃ (k + 1) sub body body' kb ksub wf₂
                (interprets_extends (tierExtends_trans ex₁ ex₂) hb)
                (interprets_extends (tierExtends_trans ex₁ ex₂) hsub) h3
              have ex₄ := allocScr_extends h
              have hw := (allocScr_wf pers wf₃ h).2
              exact decodeExpr_lookup_cell pers scr' hw
                (interprets_extends (tierExtends_trans ex₂ (tierExtends_trans ex₃ ex₄)) ih₁)
                (interprets_extends (tierExtends_trans ex₃ ex₄) ih₂)
                (interprets_extends ex₄ ih₃)

theorem scratchAbst_extends (cfg : MachineLimits) (pers : SoATier) :
    ∀ (fuel : Nat) (scr scr' : SoATier) (k fvarId : Nat) (e e' : EIdx),
      ScratchColsWF scr ->
      scratchAbst cfg pers scr fuel k fvarId e = .ok scr' e' ->
      ScratchColsWF scr' ∧ TierExtends scr scr'
  | 0, _, _, _, _, _, _, _, h => by simp [scratchAbst] at h
  | fuel + 1, scr, scr', k, fvarId, e, e', wf, h => by
    simp only [scratchAbst] at h
    cases hl : Arena.lookupNode pers scr e with
    | none => rw [hl] at h; cases h
    | some cell =>
      rw [hl] at h
      cases cell with
      | bvar _ | sort _ | const _ =>
        dsimp only at h
        simp only [ScrOp.ok.injEq] at h
        rcases h with ⟨rfl, _⟩
        exact ⟨wf, tierExtends_refl _⟩
      | fvar id =>
        dsimp only at h
        split at h
        · split at h
          · exact ⟨(allocScr_wf pers wf h).1, allocScr_extends h⟩
          · cases h
        · simp only [ScrOp.ok.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact ⟨wf, tierExtends_refl _⟩
      | app fn arg =>
        dsimp only at h
        cases h1 : scratchAbst cfg pers scr fuel k fvarId fn with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ fn' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId fn fn' wf h1
          cases h2 : scratchAbst cfg pers scr₁ fuel k fvarId arg with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ arg' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ k fvarId arg arg' wf₁ h2
            have h3 := allocScr_wf pers wf₂ h
            exact ⟨h3.1, tierExtends_trans ex₁ (tierExtends_trans ex₂ (allocScr_extends h))⟩
      | lam ty body =>
        dsimp only at h
        cases h1 : scratchAbst cfg pers scr fuel k fvarId ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId ty ty' wf h1
          cases h2 : scratchAbst cfg pers scr₁ fuel (k + 1) fvarId body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ (k + 1) fvarId body body' wf₁ h2
            have h3 := allocScr_wf pers wf₂ h
            exact ⟨h3.1, tierExtends_trans ex₁ (tierExtends_trans ex₂ (allocScr_extends h))⟩
      | forallE ty body =>
        dsimp only at h
        cases h1 : scratchAbst cfg pers scr fuel k fvarId ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId ty ty' wf h1
          cases h2 : scratchAbst cfg pers scr₁ fuel (k + 1) fvarId body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ (k + 1) fvarId body body' wf₁ h2
            have h3 := allocScr_wf pers wf₂ h
            exact ⟨h3.1, tierExtends_trans ex₁ (tierExtends_trans ex₂ (allocScr_extends h))⟩
      | letE ty val body =>
        dsimp only at h
        cases h1 : scratchAbst cfg pers scr fuel k fvarId ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId ty ty' wf h1
          cases h2 : scratchAbst cfg pers scr₁ fuel k fvarId val with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ val' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ k fvarId val val' wf₁ h2
            cases h3 : scratchAbst cfg pers scr₂ fuel (k + 1) fvarId body with
            | err _ | delegate _ => rw [h3] at h; cases h
            | ok scr₃ body' =>
              rw [h3] at h; dsimp only at h
              have ⟨wf₃, ex₃⟩ := scratchAbst_extends cfg pers fuel scr₂ scr₃ (k + 1) fvarId body body' wf₂ h3
              have h4 := allocScr_wf pers wf₃ h
              exact ⟨h4.1, tierExtends_trans ex₁
                (tierExtends_trans ex₂ (tierExtends_trans ex₃ (allocScr_extends h)))⟩

theorem scratchAbst_sound (cfg : MachineLimits) (pers : SoATier) :
    ∀ (fuel : Nat) (scr scr' : SoATier) (k fvarId : Nat) (e e' : EIdx) (ke : KExpr),
      ScratchColsWF scr ->
      Interprets pers scr e ke ->
      scratchAbst cfg pers scr fuel k fvarId e = .ok scr' e' ->
      Interprets pers scr' e' (ke.abst k fvarId)
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [scratchAbst] at h
  | fuel + 1, scr, scr', k, fvarId, e, e', ke, wf, ⟨fe, he⟩, h => by
    simp only [scratchAbst] at h
    cases hl : Arena.lookupNode pers scr e with
    | none => rw [hl] at h; cases h
    | some cell =>
      rw [hl] at h
      have hinv := decodeExpr_invert_cell pers scr he hl
      cases cell with
      | bvar _ | sort _ | const _ =>
        dsimp only at h hinv
        subst hinv
        simp only [ScrOp.ok.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨fe, by simpa [KExpr.abst] using he⟩
      | fvar id =>
        dsimp only at h hinv
        subst hinv
        split at h
        · next heq =>
          split at h
          · next hk =>
            have hw := (allocScr_wf pers wf h).2
            have hd := decodeExpr_lookup_cell pers scr' hw
            have huk : (UInt32.ofNat k).toNat = k := by
              change k % 4294967296 = k; omega
            refine ⟨1, ?_⟩
            simpa [KExpr.abst, heq, huk] using hd
          · cases h
        · next hne =>
          simp only [ScrOp.ok.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          refine ⟨fe, ?_⟩
          simpa [KExpr.abst, hne] using he
      | app fn arg =>
        dsimp only at h hinv
        rcases hinv with ⟨kfn, karg, rfl, hfn, harg⟩
        cases h1 : scratchAbst cfg pers scr fuel k fvarId fn with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ fn' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId fn fn' wf h1
          have ih₁ := scratchAbst_sound cfg pers fuel scr scr₁ k fvarId fn fn' kfn wf hfn h1
          cases h2 : scratchAbst cfg pers scr₁ fuel k fvarId arg with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ arg' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ k fvarId arg arg' wf₁ h2
            have ih₂ := scratchAbst_sound cfg pers fuel scr₁ scr₂ k fvarId arg arg' karg wf₁
              (interprets_extends ex₁ harg) h2
            have ex₃ := allocScr_extends h
            have hw := (allocScr_wf pers wf₂ h).2
            exact decodeExpr_lookup_cell pers scr' hw
              (interprets_extends (tierExtends_trans ex₂ ex₃) ih₁)
              (interprets_extends ex₃ ih₂)
      | lam ty body =>
        dsimp only at h hinv
        rcases hinv with ⟨kty, kb, rfl, hty, hb⟩
        cases h1 : scratchAbst cfg pers scr fuel k fvarId ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId ty ty' wf h1
          have ih₁ := scratchAbst_sound cfg pers fuel scr scr₁ k fvarId ty ty' kty wf hty h1
          cases h2 : scratchAbst cfg pers scr₁ fuel (k + 1) fvarId body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ (k + 1) fvarId body body' wf₁ h2
            have ih₂ := scratchAbst_sound cfg pers fuel scr₁ scr₂ (k + 1) fvarId body body' kb wf₁
              (interprets_extends ex₁ hb) h2
            have ex₃ := allocScr_extends h
            have hw := (allocScr_wf pers wf₂ h).2
            exact decodeExpr_lookup_cell pers scr' hw
              (interprets_extends (tierExtends_trans ex₂ ex₃) ih₁)
              (interprets_extends ex₃ ih₂)
      | forallE ty body =>
        dsimp only at h hinv
        rcases hinv with ⟨kty, kb, rfl, hty, hb⟩
        cases h1 : scratchAbst cfg pers scr fuel k fvarId ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId ty ty' wf h1
          have ih₁ := scratchAbst_sound cfg pers fuel scr scr₁ k fvarId ty ty' kty wf hty h1
          cases h2 : scratchAbst cfg pers scr₁ fuel (k + 1) fvarId body with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ body' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ (k + 1) fvarId body body' wf₁ h2
            have ih₂ := scratchAbst_sound cfg pers fuel scr₁ scr₂ (k + 1) fvarId body body' kb wf₁
              (interprets_extends ex₁ hb) h2
            have ex₃ := allocScr_extends h
            have hw := (allocScr_wf pers wf₂ h).2
            exact decodeExpr_lookup_cell pers scr' hw
              (interprets_extends (tierExtends_trans ex₂ ex₃) ih₁)
              (interprets_extends ex₃ ih₂)
      | letE ty val body =>
        dsimp only at h hinv
        rcases hinv with ⟨kty, kv, kb, rfl, hty, hv, hb⟩
        cases h1 : scratchAbst cfg pers scr fuel k fvarId ty with
        | err _ | delegate _ => rw [h1] at h; cases h
        | ok scr₁ ty' =>
          rw [h1] at h; dsimp only at h
          have ⟨wf₁, ex₁⟩ := scratchAbst_extends cfg pers fuel scr scr₁ k fvarId ty ty' wf h1
          have ih₁ := scratchAbst_sound cfg pers fuel scr scr₁ k fvarId ty ty' kty wf hty h1
          cases h2 : scratchAbst cfg pers scr₁ fuel k fvarId val with
          | err _ | delegate _ => rw [h2] at h; cases h
          | ok scr₂ val' =>
            rw [h2] at h; dsimp only at h
            have ⟨wf₂, ex₂⟩ := scratchAbst_extends cfg pers fuel scr₁ scr₂ k fvarId val val' wf₁ h2
            have ih₂ := scratchAbst_sound cfg pers fuel scr₁ scr₂ k fvarId val val' kv wf₁
              (interprets_extends ex₁ hv) h2
            cases h3 : scratchAbst cfg pers scr₂ fuel (k + 1) fvarId body with
            | err _ | delegate _ => rw [h3] at h; cases h
            | ok scr₃ body' =>
              rw [h3] at h; dsimp only at h
              have ⟨wf₃, ex₃⟩ := scratchAbst_extends cfg pers fuel scr₂ scr₃ (k + 1) fvarId body body' wf₂ h3
              have ih₃ := scratchAbst_sound cfg pers fuel scr₂ scr₃ (k + 1) fvarId body body' kb wf₂
                (interprets_extends (tierExtends_trans ex₁ ex₂) hb) h3
              have ex₄ := allocScr_extends h
              have hw := (allocScr_wf pers wf₃ h).2
              exact decodeExpr_lookup_cell pers scr' hw
                (interprets_extends (tierExtends_trans ex₂ (tierExtends_trans ex₃ ex₄)) ih₁)
                (interprets_extends (tierExtends_trans ex₃ ex₄) ih₂)
                (interprets_extends ex₄ ih₃)

theorem interprets_deterministic {pers scr : SoATier} {e : EIdx} {k₁ k₂ : KExpr}
    (h₁ : Interprets pers scr e k₁) (h₂ : Interprets pers scr e k₂) : k₁ = k₂ := by
  rcases h₁ with ⟨f₁, hf₁⟩
  rcases h₂ with ⟨f₂, hf₂⟩
  exact decodeExpr_deterministic pers scr hf₁ hf₂

theorem interprets_not_none {pers scr : SoATier} {e : EIdx} {ke : KExpr}
    (hi : Interprets pers scr e ke) (hl : Arena.lookupNode pers scr e = none) : False := by
  rcases hi with ⟨f, hf⟩
  cases f with
  | zero => simp [decodeExpr] at hf
  | succ f => simp [decodeExpr, hl] at hf

theorem interprets_invert (pers scr : SoATier) {e : EIdx} {c : ExprCell} {ke : KExpr}
    (hi : Interprets pers scr e ke) (hl : Arena.lookupNode pers scr e = some c) :
    match c with
    | .bvar idx => ke = .bvar idx.toNat
    | .fvar id => ke = .fvar id.toNat
    | .sort lvl => ke = .sort lvl.toNat
    | .const cid => ke = .const cid.toNat
    | .app fn arg => ∃ kfn karg, ke = .app kfn karg ∧
        Interprets pers scr fn kfn ∧ Interprets pers scr arg karg
    | .lam ty b => ∃ kty kb, ke = .lam kty kb ∧
        Interprets pers scr ty kty ∧ Interprets pers scr b kb
    | .forallE ty b => ∃ kty kb, ke = .forallE kty kb ∧
        Interprets pers scr ty kty ∧ Interprets pers scr b kb
    | .letE ty v b => ∃ kty kv kb, ke = .letE kty kv kb ∧
        Interprets pers scr ty kty ∧ Interprets pers scr v kv ∧ Interprets pers scr b kb := by
  rcases hi with ⟨f, hf⟩
  cases c with
  | bvar _ | fvar _ | sort _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ =>
    exact decodeExpr_invert_cell pers scr hf hl

theorem interprets_of_lookup (pers scr : SoATier) {e : EIdx} {c : ExprCell}
    (hl : Arena.lookupNode pers scr e = some c) :
    match c with
    | .bvar idx => Interprets pers scr e (.bvar idx.toNat)
    | .fvar id => Interprets pers scr e (.fvar id.toNat)
    | .sort lvl => Interprets pers scr e (.sort lvl.toNat)
    | .const cid => Interprets pers scr e (.const cid.toNat)
    | .app fn arg =>
      ∀ {kfn karg : KExpr}, Interprets pers scr fn kfn -> Interprets pers scr arg karg ->
        Interprets pers scr e (.app kfn karg)
    | .lam ty b =>
      ∀ {kty kb : KExpr}, Interprets pers scr ty kty -> Interprets pers scr b kb ->
        Interprets pers scr e (.lam kty kb)
    | .forallE ty b =>
      ∀ {kty kb : KExpr}, Interprets pers scr ty kty -> Interprets pers scr b kb ->
        Interprets pers scr e (.forallE kty kb)
    | .letE ty v b =>
      ∀ {kty kv kb : KExpr}, Interprets pers scr ty kty -> Interprets pers scr v kv ->
        Interprets pers scr b kb -> Interprets pers scr e (.letE kty kv kb) := by
  cases c with
  | bvar _ | fvar _ | sort _ | const _ => exact ⟨1, decodeExpr_lookup_cell pers scr hl⟩
  | app _ _ => intro _ _ h1 h2; exact decodeExpr_lookup_cell pers scr hl h1 h2
  | lam _ _ => intro _ _ h1 h2; exact decodeExpr_lookup_cell pers scr hl h1 h2
  | forallE _ _ => intro _ _ h1 h2; exact decodeExpr_lookup_cell pers scr hl h1 h2
  | letE _ _ _ => intro _ _ _ h1 h2 h3; exact decodeExpr_lookup_cell pers scr hl h1 h2 h3

/-! ### 5. O(1) DAG Guard Summary Soundness (`ExprGuardSummary`, `dagGuardSummary_sound`) -/

/-- Width of the inline universe-parameter bitmask (`64` inline parameters). -/
def lpMaskWidth : Nat := 64

/-- Summarize a node's universe-parameter indices into `(lpMask, lpOverflow)`. -/
def summarizeLParams : List Nat -> Nat × Bool
  | [] => (0, false)
  | p :: ps =>
    let (m, ov) := summarizeLParams ps
    if p < lpMaskWidth then
      (m ||| (1 <<< p), ov)
    else
      (m, true)

private theorem testBit_one_shiftLeft_eq (p q : Nat) :
    Nat.testBit (1 <<< p) q = decide (p = q) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem summarizeLParams_sound :
    ∀ (ps : List Nat),
      (summarizeLParams ps).2 = false ->
      ∀ p ∈ ps, p < lpMaskWidth ∧ Nat.testBit (summarizeLParams ps).1 p = true
  | [], _, p, hp => by cases hp
  | p₀ :: ps, hov, p, hp => by
    simp only [summarizeLParams] at hov ⊢
    split at hov
    · next hlt =>
      simp only [hlt, ↓reduceIte] at ⊢
      have hov' : (summarizeLParams ps).2 = false := hov
      rw [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · refine ⟨hlt, ?_⟩
        rw [Nat.testBit_or, testBit_one_shiftLeft_eq, decide_eq_true_eq.mpr rfl, Bool.or_true]
      · have ih := summarizeLParams_sound ps hov' p hmem
        refine ⟨ih.1, ?_⟩
        rw [Nat.testBit_or, ih.2, Bool.true_or]
    · simp at hov

/-- Bottom-up monotone O(1) DAG guard summary for a `PersTier` expression handle.
    `maxConstPos` stores `1 + max cid` over reachable constants (`0` if none), so
    `maxConstPos ≤ baseBelow` is equivalent to every constant having `cid < baseBelow`. -/
structure ExprGuardSummary where
  bvarBound : Nat
  hasFVar : Bool
  maxConstPos : Nat
  unresolvedConst : Bool
  lpMask : Nat
  lpOverflow : Bool
  deriving DecidableEq, Repr, Inhabited

def ExprGuardSummary.empty : ExprGuardSummary :=
  { bvarBound := 0
    hasFVar := false
    maxConstPos := 0
    unresolvedConst := false
    lpMask := 0
    lpOverflow := false }

/-- Monotone merge of two child summaries at the same binder depth. -/
def ExprGuardSummary.union (a b : ExprGuardSummary) : ExprGuardSummary :=
  { bvarBound := max a.bvarBound b.bvarBound
    hasFVar := a.hasFVar || b.hasFVar
    maxConstPos := max a.maxConstPos b.maxConstPos
    unresolvedConst := a.unresolvedConst || b.unresolvedConst
    lpMask := a.lpMask ||| b.lpMask
    lpOverflow := a.lpOverflow || b.lpOverflow }

/-- Step a body summary out of one binder (`lam`, `forallE`, `letE`). -/
def ExprGuardSummary.binderLift (s : ExprGuardSummary) : ExprGuardSummary :=
  { s with bvarBound := s.bvarBound - 1 }

/-- Bitmask inclusion `sub ⊆ sup` checked in O(1) bitwise arithmetic. -/
def lpMaskSubset (sub sup : Nat) : Bool :=
  (sub &&& sup) == sub

theorem lpMaskSubset_testBit {sub sup p : Nat}
    (hsub : lpMaskSubset sub sup = true)
    (ht : Nat.testBit sub p = true) :
    Nat.testBit sup p = true := by
  unfold lpMaskSubset at hsub
  rw [beq_iff_eq] at hsub
  have h1 : Nat.testBit (sub &&& sup) p = Nat.testBit sub p := congrArg (fun x => Nat.testBit x p) hsub
  rw [Nat.testBit_and, ht, Bool.true_and] at h1
  exact h1

/-- Monotonicity poset order on `ExprGuardSummary` (join semilattice). -/
structure SummaryLe (a b : ExprGuardSummary) : Prop where
  bvar : a.bvarBound ≤ b.bvarBound
  fvar : a.hasFVar = true -> b.hasFVar = true
  constPos : a.maxConstPos ≤ b.maxConstPos
  unresolved : a.unresolvedConst = true -> b.unresolvedConst = true
  lpMask : ∀ p : Nat, Nat.testBit a.lpMask p = true -> Nat.testBit b.lpMask p = true
  lpOverflow : a.lpOverflow = true -> b.lpOverflow = true

theorem SummaryLe.refl (s : ExprGuardSummary) : SummaryLe s s :=
  ⟨Nat.le_refl _, fun h => h, Nat.le_refl _, fun h => h, fun _ h => h, fun h => h⟩

theorem SummaryLe.trans {a b c : ExprGuardSummary}
    (hab : SummaryLe a b) (hbc : SummaryLe b c) : SummaryLe a c :=
  ⟨Nat.le_trans hab.bvar hbc.bvar,
   fun h => hbc.fvar (hab.fvar h),
   Nat.le_trans hab.constPos hbc.constPos,
   fun h => hbc.unresolved (hab.unresolved h),
   fun p h => hbc.lpMask p (hab.lpMask p h),
   fun h => hbc.lpOverflow (hab.lpOverflow h)⟩

theorem ExprGuardSummary.union_mono {a₁ a₂ b₁ b₂ : ExprGuardSummary}
    (ha : SummaryLe a₁ a₂) (hb : SummaryLe b₁ b₂) :
    SummaryLe (a₁.union b₁) (a₂.union b₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ExprGuardSummary.union]
    have ha1 := ha.bvar
    have hb1 := hb.bvar
    omega
  · simp only [ExprGuardSummary.union, Bool.or_eq_true]
    rintro (h | h)
    · exact Or.inl (ha.fvar h)
    · exact Or.inr (hb.fvar h)
  · simp only [ExprGuardSummary.union]
    have ha1 := ha.constPos
    have hb1 := hb.constPos
    omega
  · simp only [ExprGuardSummary.union, Bool.or_eq_true]
    rintro (h | h)
    · exact Or.inl (ha.unresolved h)
    · exact Or.inr (hb.unresolved h)
  · intro p hp
    simp only [ExprGuardSummary.union, Nat.testBit_or, Bool.or_eq_true] at hp ⊢
    rcases hp with h | h
    · exact Or.inl (ha.lpMask p h)
    · exact Or.inr (hb.lpMask p h)
  · simp only [ExprGuardSummary.union, Bool.or_eq_true]
    rintro (h | h)
    · exact Or.inl (ha.lpOverflow h)
    · exact Or.inr (hb.lpOverflow h)

theorem ExprGuardSummary.binderLift_mono {a b : ExprGuardSummary}
    (hab : SummaryLe a b) : SummaryLe a.binderLift b.binderLift :=
  ⟨(by simp only [ExprGuardSummary.binderLift]; have := hab.bvar; omega),
   hab.fvar, hab.constPos, hab.unresolved, hab.lpMask, hab.lpOverflow⟩

/-- O(1) job guard check replacing a linear/DFS traversal over the `PersTier` DAG. -/
def checkJobGuardsFast (baseBelow jobLpMask : Nat) (s : ExprGuardSummary) : Bool :=
  (s.bvarBound == 0) &&
  (!s.hasFVar) &&
  decide (s.maxConstPos ≤ baseBelow) &&
  (!s.unresolvedConst) &&
  (!s.lpOverflow) &&
  lpMaskSubset s.lpMask jobLpMask

theorem checkJobGuardsFast_antimono {baseBelow jobLpMask : Nat} {a b : ExprGuardSummary}
    (hab : SummaryLe a b)
    (hb : checkJobGuardsFast baseBelow jobLpMask b = true) :
    checkJobGuardsFast baseBelow jobLpMask a = true := by
  unfold checkJobGuardsFast at hb ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hb ⊢
  rcases hb with ⟨⟨⟨⟨⟨hbv, hfv⟩, hmc⟩, hun⟩, hov⟩, hsub⟩
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have := hab.bvar; omega
  · cases ha : a.hasFVar with
    | false => rfl
    | true => rw [hab.fvar ha] at hfv; cases hfv
  · have := hab.constPos; omega
  · cases ha : a.unresolvedConst with
    | false => rfl
    | true => rw [hab.unresolved ha] at hun; cases hun
  · cases ha : a.lpOverflow with
    | false => rfl
    | true => rw [hab.lpOverflow ha] at hov; cases hov
  · unfold lpMaskSubset at hsub ⊢
    rw [beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_and]
    cases ha : Nat.testBit a.lpMask p with
    | false => rfl
    | true =>
      have hbp : Nat.testBit b.lpMask p = true := hab.lpMask p ha
      have hj : Nat.testBit jobLpMask p = true := lpMaskSubset_testBit hsub hbp
      rw [hj, Bool.true_and]

/-- Constant resolution and universe-parameter oracle for `PersTier` nodes. -/
structure PersGuardMeta where
  constResolved : Nat -> Bool
  nodeLParams : EIdx -> List Nat

/-- Canonical guard metadata derived from a `GpuConstDecl` environment table. -/
def PersGuardMeta.ofGpuEnv (gpuEnv : Array GpuConstDecl)
    (nodeLParams : EIdx -> List Nat := fun _ => []) : PersGuardMeta :=
  { constResolved := fun cid => decide (cid < gpuEnv.size)
    nodeLParams := nodeLParams }

/-- Universe parameter indices attached to a cell at persistent handle `e`. -/
def cellLParams (gmeta : PersGuardMeta) (e : EIdx) : ExprCell -> List Nat
  | .sort _ | .const _ => gmeta.nodeLParams e
  | _ => []

/-- Bottom-up leaf summary for `.bvar`, `.fvar`, `.sort`, and `.const` cells. -/
def summarizeLeaf (gmeta : PersGuardMeta) (e : EIdx) : ExprCell -> ExprGuardSummary
  | .bvar idx =>
    { ExprGuardSummary.empty with bvarBound := idx.toNat + 1 }
  | .fvar _ =>
    { ExprGuardSummary.empty with hasFVar := true }
  | .sort _ =>
    let (m, ov) := summarizeLParams (gmeta.nodeLParams e)
    { ExprGuardSummary.empty with lpMask := m, lpOverflow := ov }
  | .const cid =>
    let (m, ov) := summarizeLParams (gmeta.nodeLParams e)
    { bvarBound := 0
      hasFVar := false
      maxConstPos := cid.toNat + 1
      unresolvedConst := !(gmeta.constResolved cid.toNat)
      lpMask := m
      lpOverflow := ov }
  | _ => ExprGuardSummary.empty

/-- Inductive well-summarized predicate relating a `PersTier` expression handle `e`
    to its bottom-up `ExprGuardSummary` computed over its child handles. -/
inductive ExprSummaryWF (pers : SoATier) (gmeta : PersGuardMeta) :
    EIdx -> ExprGuardSummary -> Prop where
  | bvar {e : EIdx} {idx : UInt32} :
      e.isPers = true ->
      pers.read e = some (.bvar idx) ->
      ExprSummaryWF pers gmeta e (summarizeLeaf gmeta e (.bvar idx))
  | fvar {e : EIdx} {id : UInt32} :
      e.isPers = true ->
      pers.read e = some (.fvar id) ->
      ExprSummaryWF pers gmeta e (summarizeLeaf gmeta e (.fvar id))
  | sort {e : EIdx} {lvl : UInt32} :
      e.isPers = true ->
      pers.read e = some (.sort lvl) ->
      ExprSummaryWF pers gmeta e (summarizeLeaf gmeta e (.sort lvl))
  | const {e : EIdx} {cid : UInt32} :
      e.isPers = true ->
      pers.read e = some (.const cid) ->
      ExprSummaryWF pers gmeta e (summarizeLeaf gmeta e (.const cid))
  | app {e fn arg : EIdx} {sFn sArg : ExprGuardSummary} :
      e.isPers = true ->
      pers.read e = some (.app fn arg) ->
      ExprSummaryWF pers gmeta fn sFn ->
      ExprSummaryWF pers gmeta arg sArg ->
      ExprSummaryWF pers gmeta e (sFn.union sArg)
  | lam {e ty body : EIdx} {sTy sBody : ExprGuardSummary} :
      e.isPers = true ->
      pers.read e = some (.lam ty body) ->
      ExprSummaryWF pers gmeta ty sTy ->
      ExprSummaryWF pers gmeta body sBody ->
      ExprSummaryWF pers gmeta e (sTy.union sBody.binderLift)
  | forallE {e ty body : EIdx} {sTy sBody : ExprGuardSummary} :
      e.isPers = true ->
      pers.read e = some (.forallE ty body) ->
      ExprSummaryWF pers gmeta ty sTy ->
      ExprSummaryWF pers gmeta body sBody ->
      ExprSummaryWF pers gmeta e (sTy.union sBody.binderLift)
  | letE {e ty val body : EIdx} {sTy sVal sBody : ExprGuardSummary} :
      e.isPers = true ->
      pers.read e = some (.letE ty val body) ->
      ExprSummaryWF pers gmeta ty sTy ->
      ExprSummaryWF pers gmeta val sVal ->
      ExprSummaryWF pers gmeta body sBody ->
      ExprSummaryWF pers gmeta e (sTy.union (sVal.union sBody.binderLift))

/-- Reachability of a `PersTier` cell `target` (at relative binder depth `d`)
    from expression root `e`. -/
inductive ReachableSub (pers : SoATier) : EIdx -> Nat -> EIdx -> ExprCell -> Prop where
  | self {e : EIdx} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some c ->
      ReachableSub pers e 0 e c
  | appFn {e fn arg target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.app fn arg) ->
      ReachableSub pers fn d target c ->
      ReachableSub pers e d target c
  | appArg {e fn arg target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.app fn arg) ->
      ReachableSub pers arg d target c ->
      ReachableSub pers e d target c
  | lamTy {e ty body target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.lam ty body) ->
      ReachableSub pers ty d target c ->
      ReachableSub pers e d target c
  | lamBody {e ty body target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.lam ty body) ->
      ReachableSub pers body d target c ->
      ReachableSub pers e (d + 1) target c
  | forallTy {e ty body target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.forallE ty body) ->
      ReachableSub pers ty d target c ->
      ReachableSub pers e d target c
  | forallBody {e ty body target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.forallE ty body) ->
      ReachableSub pers body d target c ->
      ReachableSub pers e (d + 1) target c
  | letTy {e ty val body target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.letE ty val body) ->
      ReachableSub pers ty d target c ->
      ReachableSub pers e d target c
  | letVal {e ty val body target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.letE ty val body) ->
      ReachableSub pers val d target c ->
      ReachableSub pers e d target c
  | letBody {e ty val body target : EIdx} {d : Nat} {c : ExprCell} :
      e.isPers = true ->
      pers.read e = some (.letE ty val body) ->
      ReachableSub pers body d target c ->
      ReachableSub pers e (d + 1) target c

private def CoversAt (gmeta : PersGuardMeta)
    (s : ExprGuardSummary) (depth : Nat) (target : EIdx) (cell : ExprCell) : Prop :=
  (∀ idx, cell = .bvar idx -> idx.toNat < s.bvarBound + depth) ∧
  (∀ id, cell = .fvar id -> s.hasFVar = true) ∧
  (∀ cid, cell = .const cid ->
    cid.toNat < s.maxConstPos ∧
    (gmeta.constResolved cid.toNat = false -> s.unresolvedConst = true)) ∧
  (∀ p ∈ cellLParams gmeta target cell,
    s.lpOverflow = false -> p < lpMaskWidth ∧ Nat.testBit s.lpMask p = true)

private theorem coversAt_nonleaf (gmeta : PersGuardMeta) (s : ExprGuardSummary)
    (target : EIdx) {cell : ExprCell}
    (hnb : ∀ idx, cell ≠ .bvar idx)
    (hnf : ∀ id, cell ≠ .fvar id)
    (hnc : ∀ cid, cell ≠ .const cid)
    (hnl : cellLParams gmeta target cell = []) :
    CoversAt gmeta s 0 target cell := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro idx h; exact False.elim (hnb idx h)
  · intro id h; exact False.elim (hnf id h)
  · intro cid h; exact False.elim (hnc cid h)
  · intro p hp; rw [hnl] at hp; cases hp

private theorem coversAt_union_left {gmeta : PersGuardMeta}
    {s₁ s₂ : ExprGuardSummary} {depth : Nat} {target : EIdx} {cell : ExprCell}
    (h : CoversAt gmeta s₁ depth target cell) :
    CoversAt gmeta (s₁.union s₂) depth target cell := by
  obtain ⟨hb, hf, hc, hl⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro idx hc'
    have := hb idx hc'
    simp only [ExprGuardSummary.union]; omega
  · intro id hc'
    simp only [ExprGuardSummary.union, hf id hc', Bool.true_or]
  · intro cid hc'
    obtain ⟨hlt, hun⟩ := hc cid hc'
    exact ⟨(by simp only [ExprGuardSummary.union]; omega),
           (fun hres => by simp only [ExprGuardSummary.union, hun hres, Bool.true_or])⟩
  · intro p hp hov
    simp only [ExprGuardSummary.union, Bool.or_eq_false_iff] at hov ⊢
    obtain ⟨hpw, htb⟩ := hl p hp hov.1
    exact ⟨hpw, by rw [Nat.testBit_or, htb, Bool.true_or]⟩

private theorem coversAt_union_right {gmeta : PersGuardMeta}
    {s₁ s₂ : ExprGuardSummary} {depth : Nat} {target : EIdx} {cell : ExprCell}
    (h : CoversAt gmeta s₂ depth target cell) :
    CoversAt gmeta (s₁.union s₂) depth target cell := by
  obtain ⟨hb, hf, hc, hl⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro idx hc'
    have := hb idx hc'
    simp only [ExprGuardSummary.union]; omega
  · intro id hc'
    simp only [ExprGuardSummary.union, hf id hc', Bool.or_true]
  · intro cid hc'
    obtain ⟨hlt, hun⟩ := hc cid hc'
    exact ⟨(by simp only [ExprGuardSummary.union]; omega),
           (fun hres => by simp only [ExprGuardSummary.union, hun hres, Bool.or_true])⟩
  · intro p hp hov
    simp only [ExprGuardSummary.union, Bool.or_eq_false_iff] at hov ⊢
    obtain ⟨hpw, htb⟩ := hl p hp hov.2
    exact ⟨hpw, by rw [Nat.testBit_or, htb, Bool.or_true]⟩

private theorem coversAt_binderLift {gmeta : PersGuardMeta}
    {s : ExprGuardSummary} {depth : Nat} {target : EIdx} {cell : ExprCell}
    (h : CoversAt gmeta s depth target cell) :
    CoversAt gmeta s.binderLift (depth + 1) target cell := by
  obtain ⟨hb, hf, hc, hl⟩ := h
  refine ⟨?_, hf, hc, hl⟩
  intro idx hc'
  have := hb idx hc'
  simp only [ExprGuardSummary.binderLift]
  omega

private theorem exprSummaryWF_covers {pers : SoATier} {gmeta : PersGuardMeta}
    {e : EIdx} {s : ExprGuardSummary} (hwf : ExprSummaryWF pers gmeta e s) :
    ∀ {depth : Nat} {target : EIdx} {cell : ExprCell},
      ReachableSub pers e depth target cell ->
      CoversAt gmeta s depth target cell := by
  induction hwf with
  | bvar hp hr =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      refine ⟨(fun idx h => by cases h; simp [summarizeLeaf]),
              (fun _ h => by cases h),
              (fun _ h => by cases h),
              (fun p hp => by simp [cellLParams] at hp)⟩
    | appFn _ hr' _ | appArg _ hr' _ | lamTy _ hr' _ | lamBody _ hr' _
    | forallTy _ hr' _ | forallBody _ hr' _ | letTy _ hr' _ | letVal _ hr' _
    | letBody _ hr' _ => rw [hr] at hr'; cases hr'
  | fvar hp hr =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      refine ⟨(fun _ h => by cases h),
              (fun _ _ => by simp [summarizeLeaf]),
              (fun _ h => by cases h),
              (fun p hp => by simp [cellLParams] at hp)⟩
    | appFn _ hr' _ | appArg _ hr' _ | lamTy _ hr' _ | lamBody _ hr' _
    | forallTy _ hr' _ | forallBody _ hr' _ | letTy _ hr' _ | letVal _ hr' _
    | letBody _ hr' _ => rw [hr] at hr'; cases hr'
  | sort hp hr =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      refine ⟨(fun _ h => by cases h),
              (fun _ h => by cases h),
              (fun _ h => by cases h),
              (fun p hp hov => by
                simp only [cellLParams] at hp
                simp only [summarizeLeaf] at hov ⊢
                exact summarizeLParams_sound _ hov p hp)⟩
    | appFn _ hr' _ | appArg _ hr' _ | lamTy _ hr' _ | lamBody _ hr' _
    | forallTy _ hr' _ | forallBody _ hr' _ | letTy _ hr' _ | letVal _ hr' _
    | letBody _ hr' _ => rw [hr] at hr'; cases hr'
  | const hp hr =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      refine ⟨(fun _ h => by cases h),
              (fun _ h => by cases h),
              (fun cid' h => by
                cases h
                simp only [summarizeLeaf]
                exact ⟨by omega, fun hres => by simp [hres]⟩),
              (fun p hp hov => by
                simp only [cellLParams] at hp
                simp only [summarizeLeaf] at hov ⊢
                exact summarizeLParams_sound _ hov p hp)⟩
    | appFn _ hr' _ | appArg _ hr' _ | lamTy _ hr' _ | lamBody _ hr' _
    | forallTy _ hr' _ | forallBody _ hr' _ | letTy _ hr' _ | letVal _ hr' _
    | letBody _ hr' _ => rw [hr] at hr'; cases hr'
  | @app e fn arg sFn sArg hp hr hfn harg ihFn ihArg =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      exact coversAt_nonleaf gmeta _ _ (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h) rfl
    | appFn _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_left (ihFn hsub)
    | appArg _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_right (ihArg hsub)
    | lamTy _ hr' _ | lamBody _ hr' _ | forallTy _ hr' _ | forallBody _ hr' _
    | letTy _ hr' _ | letVal _ hr' _ | letBody _ hr' _ => rw [hr] at hr'; cases hr'
  | @lam e ty body sTy sBody hp hr hty hbody ihTy ihBody =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      exact coversAt_nonleaf gmeta _ _ (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h) rfl
    | lamTy _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_left (ihTy hsub)
    | lamBody _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_right (coversAt_binderLift (ihBody hsub))
    | appFn _ hr' _ | appArg _ hr' _ | forallTy _ hr' _ | forallBody _ hr' _
    | letTy _ hr' _ | letVal _ hr' _ | letBody _ hr' _ => rw [hr] at hr'; cases hr'
  | @forallE e ty body sTy sBody hp hr hty hbody ihTy ihBody =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      exact coversAt_nonleaf gmeta _ _ (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h) rfl
    | forallTy _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_left (ihTy hsub)
    | forallBody _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_right (coversAt_binderLift (ihBody hsub))
    | appFn _ hr' _ | appArg _ hr' _ | lamTy _ hr' _ | lamBody _ hr' _
    | letTy _ hr' _ | letVal _ hr' _ | letBody _ hr' _ => rw [hr] at hr'; cases hr'
  | @letE e ty val body sTy sVal sBody hp hr hty hval hbody ihTy ihVal ihBody =>
    intro depth target cell hreach
    cases hreach with
    | self _ hr' =>
      rw [hr] at hr'; injection hr' with hcell; subst hcell
      exact coversAt_nonleaf gmeta _ _ (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h) rfl
    | letTy _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_left (ihTy hsub)
    | letVal _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_right (coversAt_union_left (ihVal hsub))
    | letBody _ hr' hsub =>
      rw [hr] at hr'; injection hr' with heq; cases heq
      exact coversAt_union_right (coversAt_union_right (coversAt_binderLift (ihBody hsub)))
    | appFn _ hr' _ | appArg _ hr' _ | lamTy _ hr' _ | lamBody _ hr' _
    | forallTy _ hr' _ | forallBody _ hr' _ => rw [hr] at hr'; cases hr'

/-- Main O(1) DAG Guard Summary Soundness Theorem:
    If `checkJobGuardsFast baseBelow jobLpMask s = true` holds on a bottom-up
    well-summarized handle `e`, then `s.bvarBound = 0`, `s.hasFVar = false`,
    no loose bound variables or free variables are reachable from `e`, every
    reachable `.const cid` satisfies `cid.toNat < baseBelow` and is resolved,
    and every reachable universe parameter falls within `jobLpMask` without overflow. -/
theorem dagGuardSummary_sound {pers : SoATier} {gmeta : PersGuardMeta}
    {e : EIdx} {s : ExprGuardSummary} {baseBelow jobLpMask : Nat}
    (hwf : ExprSummaryWF pers gmeta e s)
    (hfast : checkJobGuardsFast baseBelow jobLpMask s = true) :
    s.bvarBound = 0 ∧
    s.hasFVar = false ∧
    (∀ d target idx, ReachableSub pers e d target (.bvar idx) -> idx.toNat < d) ∧
    (∀ d target id, ¬ ReachableSub pers e d target (.fvar id)) ∧
    (∀ d target cid, ReachableSub pers e d target (.const cid) ->
      cid.toNat < baseBelow ∧ gmeta.constResolved cid.toNat = true) ∧
    (∀ d target cell p, ReachableSub pers e d target cell ->
      p ∈ cellLParams gmeta target cell ->
      p < lpMaskWidth ∧ Nat.testBit jobLpMask p = true) := by
  have hfast' := hfast
  unfold checkJobGuardsFast at hfast'
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hfast'
  rcases hfast' with ⟨⟨⟨⟨⟨hbv, hfv⟩, hmc⟩, hun⟩, hov⟩, hsub⟩
  refine ⟨hbv, hfv, ?_, ?_, ?_, ?_⟩
  · intro d target idx hreach
    have hc := (exprSummaryWF_covers hwf hreach).1 idx rfl
    omega
  · intro d target id hreach
    have hc := (exprSummaryWF_covers hwf hreach).2.1 id rfl
    rw [hc] at hfv
    cases hfv
  · intro d target cid hreach
    have hc := (exprSummaryWF_covers hwf hreach).2.2.1 cid rfl
    refine ⟨(by omega), ?_⟩
    cases hres : gmeta.constResolved cid.toNat with
    | true => rfl
    | false =>
      rw [hc.2 hres] at hun
      cases hun
  · intro d target cell p hreach hp
    obtain ⟨hpw, htb⟩ := (exprSummaryWF_covers hwf hreach).2.2.2 p hp hov
    exact ⟨hpw, lpMaskSubset_testBit hsub htb⟩

/-- Bottom-up local consistency of a precomputed summary table `sumOf` at handle `e`. -/
def PersDagSummaryStep (pers : SoATier) (gmeta : PersGuardMeta)
    (sumOf : EIdx -> ExprGuardSummary) (e : EIdx) : Prop :=
  e.isPers = true ∧
  match pers.read e with
  | none => False
  | some (.bvar idx) => sumOf e = summarizeLeaf gmeta e (.bvar idx)
  | some (.fvar id) => sumOf e = summarizeLeaf gmeta e (.fvar id)
  | some (.sort lvl) => sumOf e = summarizeLeaf gmeta e (.sort lvl)
  | some (.const cid) => sumOf e = summarizeLeaf gmeta e (.const cid)
  | some (.app fn arg) => sumOf e = (sumOf fn).union (sumOf arg)
  | some (.lam ty body) => sumOf e = (sumOf ty).union (sumOf body).binderLift
  | some (.forallE ty body) => sumOf e = (sumOf ty).union (sumOf body).binderLift
  | some (.letE ty val body) =>
    sumOf e = (sumOf ty).union ((sumOf val).union (sumOf body).binderLift)

private theorem empty_read_none (e : EIdx) : SoATier.empty.read e = none := by
  unfold SoATier.read SoATier.empty
  by_cases hw : e.isWide <;> simp [hw] <;> split <;> simp <;> split <;> simp

private theorem isPers_of_decodeExpr_empty {pers : SoATier} {fuel : Nat} {h : EIdx} {kh : KExpr}
    (hd : decodeExpr pers .empty fuel h = some kh) : h.isPers = true := by
  cases fuel with
  | zero => simp [decodeExpr] at hd
  | succ f =>
    cases hpf : h.isPers with
    | true => rfl
    | false =>
      simp only [decodeExpr, Arena.lookupNode, hpf, Bool.false_eq_true, ↓reduceIte,
        empty_read_none] at hd
      cases hd

theorem exprSummaryWF_of_fuel (pers : SoATier) (gmeta : PersGuardMeta)
    (sumOf : EIdx -> ExprGuardSummary)
    (hstep : ∀ h, h.isPers = true -> (pers.read h).isSome -> PersDagSummaryStep pers gmeta sumOf h) :
    ∀ (fuel : Nat) (e : EIdx) (ke : KExpr),
      e.isPers = true ->
      decodeExpr pers .empty fuel e = some ke ->
      ExprSummaryWF pers gmeta e (sumOf e)
  | 0, _, _, _, hd => by simp [decodeExpr] at hd
  | fuel + 1, e, ke, hep, hd => by
    simp only [decodeExpr, Arena.lookupNode, hep, ↓reduceIte] at hd
    cases hr : pers.read e with
    | none => rw [hr] at hd; cases hd
    | some c =>
      rw [hr] at hd
      have hsum := (hstep e hep (by simp [hr])).2
      rw [hr] at hsum
      cases c with
      | bvar idx => rw [hsum]; exact ExprSummaryWF.bvar hep hr
      | fvar id => rw [hsum]; exact ExprSummaryWF.fvar hep hr
      | sort lvl => rw [hsum]; exact ExprSummaryWF.sort hep hr
      | const cid => rw [hsum]; exact ExprSummaryWF.const hep hr
      | app fn arg =>
        dsimp only at hd
        cases hfn : decodeExpr pers .empty fuel fn <;> rw [hfn] at hd
        · cases hd
        cases harg : decodeExpr pers .empty fuel arg <;> rw [harg] at hd
        · cases hd
        rw [hsum]
        exact ExprSummaryWF.app hep hr
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel fn _
            (isPers_of_decodeExpr_empty hfn) hfn)
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel arg _
            (isPers_of_decodeExpr_empty harg) harg)
      | lam ty body =>
        dsimp only at hd
        cases hty : decodeExpr pers .empty fuel ty <;> rw [hty] at hd
        · cases hd
        cases hb : decodeExpr pers .empty fuel body <;> rw [hb] at hd
        · cases hd
        rw [hsum]
        exact ExprSummaryWF.lam hep hr
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel ty _
            (isPers_of_decodeExpr_empty hty) hty)
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel body _
            (isPers_of_decodeExpr_empty hb) hb)
      | forallE ty body =>
        dsimp only at hd
        cases hty : decodeExpr pers .empty fuel ty <;> rw [hty] at hd
        · cases hd
        cases hb : decodeExpr pers .empty fuel body <;> rw [hb] at hd
        · cases hd
        rw [hsum]
        exact ExprSummaryWF.forallE hep hr
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel ty _
            (isPers_of_decodeExpr_empty hty) hty)
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel body _
            (isPers_of_decodeExpr_empty hb) hb)
      | letE ty val body =>
        dsimp only at hd
        cases hty : decodeExpr pers .empty fuel ty <;> rw [hty] at hd
        · cases hd
        cases hv : decodeExpr pers .empty fuel val <;> rw [hv] at hd
        · cases hd
        cases hb : decodeExpr pers .empty fuel body <;> rw [hb] at hd
        · cases hd
        rw [hsum]
        exact ExprSummaryWF.letE hep hr
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel ty _
            (isPers_of_decodeExpr_empty hty) hty)
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel val _
            (isPers_of_decodeExpr_empty hv) hv)
          (exprSummaryWF_of_fuel pers gmeta sumOf hstep fuel body _
            (isPers_of_decodeExpr_empty hb) hb)

/-! ### 6. Exact 64-bit Limb-Pair Arithmetic (`UInt32 × UInt32`) -/

/-- Little-endian 64-bit natural number represented as a `(lo, hi)` `UInt32` limb pair. -/
abbrev Nat64 := UInt32 × UInt32

/-- Mathematical value of a `Nat64` limb pair. -/
def Nat64.toNat (x : Nat64) : Nat :=
  x.1.toNat + x.2.toNat * 2 ^ 32

private theorem ui32_lt_2p32 (x : UInt32) : x.toNat < 2 ^ 32 :=
  x.toNat_lt_size

theorem nat64_toNat_lt (x : Nat64) : x.toNat < 2 ^ 64 := by
  have h1 : x.1.toNat < 2 ^ 32 := ui32_lt_2p32 x.1
  have h2 : x.2.toNat < 2 ^ 32 := ui32_lt_2p32 x.2
  unfold Nat64.toNat
  omega

private theorem ui32_eq_of_toNat_eq {x y : UInt32} (h : x.toNat = y.toNat) : x = y := by
  have hx : UInt32.ofNat x.toNat = x := UInt32.ofNat_toNat
  have hy : UInt32.ofNat y.toNat = y := UInt32.ofNat_toNat
  rw [← hx, ← hy, h]

def nat64Zero : Nat64 := (0, 0)

theorem nat64Zero_toNat : nat64Zero.toNat = 0 := by
  simp [nat64Zero, Nat64.toNat]

def nat64IsZero (a : Nat64) : Bool :=
  a.1 == 0 && a.2 == 0

theorem nat64IsZero_iff (a : Nat64) : nat64IsZero a = true ↔ a.toNat = 0 := by
  unfold nat64IsZero Nat64.toNat
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    simp [h1, h2]
  · intro h
    have h1 : a.1.toNat = 0 := by omega
    have h2 : a.2.toNat = 0 := by omega
    exact ⟨ui32_eq_of_toNat_eq (by simpa using h1), ui32_eq_of_toNat_eq (by simpa using h2)⟩

def nat64Lt (a b : Nat64) : Bool :=
  a.2 < b.2 || (a.2 == b.2 && a.1 < b.1)

theorem nat64Lt_iff (a b : Nat64) : nat64Lt a b = true ↔ a.toNat < b.toNat := by
  unfold nat64Lt Nat64.toNat
  have ha1 : a.1.toNat < 2 ^ 32 := ui32_lt_2p32 a.1
  have hb1 : b.1.toNat < 2 ^ 32 := ui32_lt_2p32 b.1
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with hlt | ⟨heq, hlt⟩
    · change a.2.toNat < b.2.toNat at hlt
      omega
    · have : a.2.toNat = b.2.toNat := congrArg UInt32.toNat heq
      change a.1.toNat < b.1.toNat at hlt
      omega
  · intro h
    by_cases hlt2 : a.2.toNat < b.2.toNat
    · exact Or.inl hlt2
    · have heq2 : a.2.toNat = b.2.toNat := by omega
      have hlt1 : a.1.toNat < b.1.toNat := by omega
      exact Or.inr ⟨ui32_eq_of_toNat_eq heq2, hlt1⟩

/-- Saturating 64-bit limb-pair subtraction (`0` when `a <= b`), matching WGSL `nat_sub_u64`. -/
def nat64Sub (a b : Nat64) : Nat64 :=
  if a.2 < b.2 || (a.2 == b.2 && a.1 <= b.1) then (0, 0)
  else
    let borrow : UInt32 := if a.1 < b.1 then 1 else 0
    (a.1 - b.1, a.2 - b.2 - borrow)

/-- Wrapping 64-bit limb-pair subtraction modulo `2^64`. -/
def nat64SubWrap (a b : Nat64) : Nat64 :=
  let borrow : UInt32 := if a.1 < b.1 then 1 else 0
  (a.1 - b.1, a.2 - b.2 - borrow)

private theorem ui32_sub_eq_of_le {x y : UInt32} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  have hx : x.toNat < 2 ^ 32 := ui32_lt_2p32 x
  have hy : y.toNat < 2 ^ 32 := ui32_lt_2p32 y
  rw [UInt32.toNat_sub]
  change (2 ^ 32 - y.toNat + x.toNat) % 2 ^ 32 = x.toNat - y.toNat
  have heq : 2 ^ 32 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 32 := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem ui32_sub_eq_of_lt {x y : UInt32} (h : x.toNat < y.toNat) :
    (x - y).toNat = 2 ^ 32 + x.toNat - y.toNat := by
  have hx : x.toNat < 2 ^ 32 := ui32_lt_2p32 x
  have hy : y.toNat < 2 ^ 32 := ui32_lt_2p32 y
  rw [UInt32.toNat_sub]
  change (2 ^ 32 - y.toNat + x.toNat) % 2 ^ 32 = 2 ^ 32 + x.toNat - y.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem nat64Sub_correct (a b : Nat64) : (nat64Sub a b).toNat = a.toNat - b.toNat := by
  unfold nat64Sub Nat64.toNat
  have ha1 : a.1.toNat < 2 ^ 32 := ui32_lt_2p32 a.1
  have hb1 : b.1.toNat < 2 ^ 32 := ui32_lt_2p32 b.1
  split
  · next hle =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hle
    have hab : a.toNat ≤ b.toNat := by
      rcases hle with hlt | ⟨heq, h1⟩
      · change a.2.toNat < b.2.toNat at hlt
        unfold Nat64.toNat; omega
      · have heqn : a.2.toNat = b.2.toNat := congrArg UInt32.toNat heq
        change a.1.toNat ≤ b.1.toNat at h1
        unfold Nat64.toNat; omega
    unfold Nat64.toNat at hab
    simp only [UInt32.toNat_zero]
    omega
  · next hgt =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_and] at hgt
    obtain ⟨hge2, hnot1⟩ := hgt
    have ha2b2 : b.2.toNat ≤ a.2.toNat := by
      change ¬ a.2.toNat < b.2.toNat at hge2
      omega
    dsimp only
    by_cases hlt1 : a.1 < b.1
    · have hlt1n : a.1.toNat < b.1.toNat := hlt1
      have hne2 : a.2.toNat ≠ b.2.toNat := by
        intro heq
        have h1 : ¬ a.1.toNat ≤ b.1.toNat := hnot1 (ui32_eq_of_toNat_eq heq)
        omega
      have hsub1 : (a.1 - b.1).toNat = 2 ^ 32 + a.1.toNat - b.1.toNat := ui32_sub_eq_of_lt hlt1n
      have hsub2a : (a.2 - b.2).toNat = a.2.toNat - b.2.toNat := ui32_sub_eq_of_le ha2b2
      have hle1 : (1 : UInt32).toNat ≤ (a.2 - b.2).toNat := by
        rw [hsub2a]; simp; omega
      have hsub2 : (a.2 - b.2 - 1).toNat = (a.2 - b.2).toNat - 1 := ui32_sub_eq_of_le hle1
      simp only [hlt1, ↓reduceIte, hsub1, hsub2, hsub2a]
      omega
    · have hge1 : b.1.toNat ≤ a.1.toNat := by
        change ¬ a.1.toNat < b.1.toNat at hlt1
        omega
      have hsub1 : (a.1 - b.1).toNat = a.1.toNat - b.1.toNat := ui32_sub_eq_of_le hge1
      have hsub2a : (a.2 - b.2).toNat = a.2.toNat - b.2.toNat := ui32_sub_eq_of_le ha2b2
      simp only [hlt1, ↓reduceIte, hsub1, UInt32.sub_zero, hsub2a]
      omega

theorem nat64SubWrap_correct_of_ge {a b : Nat64} (h : b.toNat ≤ a.toNat) :
    (nat64SubWrap a b).toNat = a.toNat - b.toNat := by
  unfold nat64SubWrap Nat64.toNat
  unfold Nat64.toNat at h
  have ha1 : a.1.toNat < 2 ^ 32 := ui32_lt_2p32 a.1
  have hb1 : b.1.toNat < 2 ^ 32 := ui32_lt_2p32 b.1
  by_cases hlt1 : a.1 < b.1
  · have hlt1n : a.1.toNat < b.1.toNat := hlt1
    have hlt2 : b.2.toNat < a.2.toNat := by omega
    have hsub1 : (a.1 - b.1).toNat = 2 ^ 32 + a.1.toNat - b.1.toNat := ui32_sub_eq_of_lt hlt1n
    have hsub2a : (a.2 - b.2).toNat = a.2.toNat - b.2.toNat := ui32_sub_eq_of_le (Nat.le_of_lt hlt2)
    have hsub2 : (a.2 - b.2 - 1).toNat = (a.2 - b.2).toNat - 1 := by
      apply ui32_sub_eq_of_le; rw [hsub2a]; simp; omega
    simp only [hlt1, ↓reduceIte, hsub1, hsub2, hsub2a]
    omega
  · have hge1 : b.1.toNat ≤ a.1.toNat := by
      change ¬ a.1.toNat < b.1.toNat at hlt1
      omega
    have hle2 : b.2.toNat ≤ a.2.toNat := by omega
    have hsub1 : (a.1 - b.1).toNat = a.1.toNat - b.1.toNat := ui32_sub_eq_of_le hge1
    have hsub2a : (a.2 - b.2).toNat = a.2.toNat - b.2.toNat := ui32_sub_eq_of_le hle2
    simp only [hlt1, ↓reduceIte, hsub1, UInt32.sub_zero, hsub2a]
    omega

theorem nat64SubWrap_correct_of_lt_borrow {a b : Nat64} (h : a.toNat < b.toNat) :
    (nat64SubWrap a b).toNat = 2 ^ 64 + a.toNat - b.toNat := by
  unfold nat64SubWrap Nat64.toNat
  unfold Nat64.toNat at h
  have ha1 : a.1.toNat < 2 ^ 32 := ui32_lt_2p32 a.1
  have hb1 : b.1.toNat < 2 ^ 32 := ui32_lt_2p32 b.1
  have ha2 : a.2.toNat < 2 ^ 32 := ui32_lt_2p32 a.2
  have hb2 : b.2.toNat < 2 ^ 32 := ui32_lt_2p32 b.2
  have hpow64 : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
  by_cases hlt1 : a.1 < b.1
  · have hlt1n : a.1.toNat < b.1.toNat := hlt1
    have hle2 : a.2.toNat ≤ b.2.toNat := by omega
    have hsub1 : (a.1 - b.1).toNat = 2 ^ 32 + a.1.toNat - b.1.toNat := ui32_sub_eq_of_lt hlt1n
    by_cases heq2 : a.2.toNat = b.2.toNat
    · have hsub2a : (a.2 - b.2).toNat = 0 := by
        rw [ui32_sub_eq_of_le (by omega)]; omega
      have hsub2 : (a.2 - b.2 - 1).toNat = 2 ^ 32 - 1 := by
        have hltz : (a.2 - b.2).toNat < (1 : UInt32).toNat := by rw [hsub2a]; simp
        rw [ui32_sub_eq_of_lt hltz, hsub2a]; simp
      simp only [hlt1, ↓reduceIte, hsub1, hsub2]
      omega
    · have hlt2 : a.2.toNat < b.2.toNat := by omega
      have hsub2a : (a.2 - b.2).toNat = 2 ^ 32 + a.2.toNat - b.2.toNat := ui32_sub_eq_of_lt hlt2
      have hge1' : (1 : UInt32).toNat ≤ (a.2 - b.2).toNat := by
        rw [hsub2a]; simp; omega
      have hsub2 : (a.2 - b.2 - 1).toNat = (a.2 - b.2).toNat - 1 := ui32_sub_eq_of_le hge1'
      simp only [hlt1, ↓reduceIte, hsub1, hsub2, hsub2a]
      omega
  · have hge1 : b.1.toNat ≤ a.1.toNat := by
      change ¬ a.1.toNat < b.1.toNat at hlt1
      omega
    have hlt2 : a.2.toNat < b.2.toNat := by omega
    have hsub1 : (a.1 - b.1).toNat = a.1.toNat - b.1.toNat := ui32_sub_eq_of_le hge1
    have hsub2a : (a.2 - b.2).toNat = 2 ^ 32 + a.2.toNat - b.2.toNat := ui32_sub_eq_of_lt hlt2
    simp only [hlt1, ↓reduceIte, hsub1, UInt32.sub_zero, hsub2a]
    omega

/-- Exact 64-bit saturating predecessor (`a - 1`, returning `0` on `0`). -/
def nat64Pred (a : Nat64) : Nat64 :=
  nat64Sub a (1, 0)

theorem nat64Pred_correct (a : Nat64) : (nat64Pred a).toNat = a.toNat - 1 := by
  unfold nat64Pred
  rw [nat64Sub_correct]
  simp [Nat64.toNat]

private theorem ui32_shiftRight_toNat (x k : UInt32) (hk : k.toNat < 32) :
    (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

private theorem ui32_shiftLeft_toNat (x k : UInt32) (hk : k.toNat < 32) :
    (x <<< k).toNat = (x.toNat * 2 ^ k.toNat) % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq]

private theorem ui32_or_disjoint_toNat {x y : UInt32} {k : Nat}
    (hx : x.toNat < 2 ^ k) (hy : ∃ m, y.toNat = m * 2 ^ k) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  rcases hy with ⟨m, hm⟩
  rw [UInt32.toNat_or, hm]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  have htest (n j : Nat) : n.testBit j = ((n / 2 ^ j) % 2 == 1) := by
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  simp only [htest]
  by_cases hi : i < k
  · have hkpos : 0 < 2 ^ i := Nat.pow_pos (by decide)
    have hpow : 2 ^ k = (2 ^ (k - i) * 2 ^ i) := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hi)]
    have hydiv : (m * 2 ^ k) / 2 ^ i = m * 2 ^ (k - i) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_div_cancel _ hkpos]
    have h2sub : 2 ^ (k - i) = 2 ^ (k - i - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    have hy0 : ((m * 2 ^ k) / 2 ^ i % 2 == 1) = false := by
      rw [hydiv, h2sub, ← Nat.mul_assoc]
      have hmod : (m * 2 ^ (k - i - 1) * 2) % 2 = 0 := Nat.mul_mod_left _ 2
      simp [hmod]
    have hsum : (x.toNat + m * 2 ^ k) / 2 ^ i = x.toNat / 2 ^ i + m * 2 ^ (k - i) := by
      rw [hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ hkpos]
    have hsum_mod : (x.toNat + m * 2 ^ k) / 2 ^ i % 2 = x.toNat / 2 ^ i % 2 := by
      rw [hsum, h2sub, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    rw [hy0, Bool.or_false, hsum_mod]
  · have hki : k ≤ i := Nat.le_of_not_lt hi
    have hpowk : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hki]
    have hxlt : x.toNat < 2 ^ i := by
      have : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hki
      omega
    have hx0b : (x.toNat / 2 ^ i % 2 == 1) = false := by
      rw [Nat.div_eq_of_lt hxlt]; simp
    have hsum : (x.toNat + m * 2 ^ k) / 2 ^ i = (m * 2 ^ k) / 2 ^ i := by
      rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      rw [Nat.add_comm x.toNat, Nat.mul_comm m (2 ^ k), Nat.mul_add_div hpowk,
        Nat.div_eq_of_lt hx, Nat.mul_div_cancel_left _ hpowk]
      simp
    rw [hx0b, Bool.false_or, hsum]

private theorem ui32_shiftLeft_low_mul {x k : UInt32} (hk : k.toNat < 32) :
    (x <<< k).toNat = (x.toNat % 2 ^ (32 - k.toNat)) * 2 ^ k.toNat := by
  have hk0 : 0 < 2 ^ k.toNat := Nat.pow_pos (by decide)
  have hsub0 : 0 < 2 ^ (32 - k.toNat) := Nat.pow_pos (by decide)
  let q := x.toNat / 2 ^ (32 - k.toNat)
  let r := x.toNat % 2 ^ (32 - k.toNat)
  have hxeq : x.toNat = q * 2 ^ (32 - k.toNat) + r := by
    dsimp only [q, r]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod x.toNat (2 ^ (32 - k.toNat))).symm
  have hpow : 2 ^ (32 - k.toNat) * 2 ^ k.toNat = 2 ^ 32 := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk)]
  have hrlt : r < 2 ^ (32 - k.toNat) := Nat.mod_lt _ hsub0
  have hbound : r * 2 ^ k.toNat < 2 ^ 32 := by
    have hmul := Nat.mul_le_mul_right (2 ^ k.toNat) (Nat.succ_le_of_lt hrlt)
    rw [Nat.succ_mul, hpow] at hmul
    omega
  calc (x <<< k).toNat
      = ((q * 2 ^ (32 - k.toNat) + r) * 2 ^ k.toNat) % 2 ^ 32 := by
        rw [ui32_shiftLeft_toNat x k hk, hxeq]
    _ = (q * 2 ^ 32 + r * 2 ^ k.toNat) % 2 ^ 32 := by
        rw [Nat.add_mul, Nat.mul_assoc, hpow]
    _ = (r * 2 ^ k.toNat) % 2 ^ 32 := by
        rw [Nat.mul_comm q (2 ^ 32), Nat.mul_add_mod]
    _ = r * 2 ^ k.toNat := Nat.mod_eq_of_lt hbound

/-- Exact 64-bit logical right shift, returning `(0, 0)` whenever `s >= 64`. -/
def nat64Shr (a s : Nat64) : Nat64 :=
  if s.2 != 0 || s.1 >= 64 then (0, 0)
  else
    let k := s.1
    if k == 0 then a
    else if k < 32 then
      ((a.1 >>> k) ||| (a.2 <<< (32 - k)), a.2 >>> k)
    else if k == 32 then
      (a.2, 0)
    else
      (a.2 >>> (k - 32), 0)

theorem nat64Shr_ge64 {a s : Nat64} (hs : 64 ≤ s.toNat) : nat64Shr a s = (0, 0) := by
  unfold nat64Shr
  have hcond : (s.2 != 0 || decide (64 ≤ s.1)) = true := by
    by_cases hs2 : s.2 = 0
    · have hs1 : 64 ≤ s.1.toNat := by
        unfold Nat64.toNat at hs; rw [hs2] at hs; simpa using hs
      have hdec : decide ((64 : UInt32) ≤ s.1) = true := decide_eq_true hs1
      simp [hdec]
    · simp [hs2]
  simp [hcond]

theorem nat64Shr_correct (a s : Nat64) : (nat64Shr a s).toNat = a.toNat >>> s.toNat := by
  rw [Nat.shiftRight_eq_div_pow]
  by_cases hs64 : 64 ≤ s.toNat
  · rw [nat64Shr_ge64 hs64]
    have ha : a.toNat < 2 ^ 64 := nat64_toNat_lt a
    have hpow : 2 ^ 64 ≤ 2 ^ s.toNat := Nat.pow_le_pow_right (by decide) hs64
    have hz : a.toNat / 2 ^ s.toNat = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le ha hpow)
    rw [hz]
    simp [Nat64.toNat]
  · have hs2 : s.2 = 0 := by
      by_cases hne : s.2 = 0
      · exact hne
      · have hpos : 1 ≤ s.2.toNat := by
          have hnz : s.2.toNat ≠ 0 := fun hz => hne (ui32_eq_of_toNat_eq (by simpa using hz))
          omega
        unfold Nat64.toNat at hs64
        have : (2 ^ 32 : Nat) ≤ s.2.toNat * 2 ^ 32 := Nat.le_mul_of_pos_left _ hpos
        omega
    have hk64 : s.1.toNat < 64 := by
      unfold Nat64.toNat at hs64
      rw [hs2] at hs64
      simp only [UInt32.toNat_zero, Nat.zero_mul, Nat.add_zero] at hs64
      omega
    have hs_nat : s.toNat = s.1.toNat := by
      unfold Nat64.toNat; rw [hs2]; simp
    have hcond : (s.2 != 0 || decide (64 ≤ s.1)) = false := by
      simp only [hs2, bne_self_eq_false, Bool.false_or, decide_eq_false_iff_not]
      change ¬ 64 ≤ s.1.toNat
      omega
    unfold nat64Shr
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, hs_nat]
    by_cases hk0 : s.1 = 0
    · simp only [hk0, beq_self_eq_true, ↓reduceIte, UInt32.toNat_zero, Nat.pow_zero, Nat.div_one]
    · have hk0n : s.1.toNat ≠ 0 := fun hz => hk0 (ui32_eq_of_toNat_eq (by simpa using hz))
      have hbeq0 : (s.1 == 0) = false := beq_false_of_ne hk0
      simp only [hbeq0, Bool.false_eq_true, ↓reduceIte]
      by_cases hk32 : s.1 < 32
      · simp only [hk32, ↓reduceIte]
        have hk32n : s.1.toNat < 32 := hk32
        have hsub : (32 - s.1).toNat = 32 - s.1.toNat := by
          apply ui32_sub_eq_of_le; change s.1.toNat ≤ (32 : UInt32).toNat; simp; omega
        have hsub32 : (32 - s.1).toNat < 32 := by rw [hsub]; omega
        have ha1_shr : (a.1 >>> s.1).toNat = a.1.toNat / 2 ^ s.1.toNat :=
          ui32_shiftRight_toNat a.1 s.1 hk32n
        have ha2_shr : (a.2 >>> s.1).toNat = a.2.toNat / 2 ^ s.1.toNat :=
          ui32_shiftRight_toNat a.2 s.1 hk32n
        have hsub_sub : 32 - (32 - s.1.toNat) = s.1.toNat := by omega
        have ha2_shl : (a.2 <<< (32 - s.1)).toNat =
            (a.2.toNat % 2 ^ s.1.toNat) * 2 ^ (32 - s.1.toNat) := by
          rw [ui32_shiftLeft_low_mul hsub32, hsub, hsub_sub]
        have ha1_lt : (a.1 >>> s.1).toNat < 2 ^ (32 - s.1.toNat) := by
          rw [ha1_shr]
          have ha1 : a.1.toNat < 2 ^ 32 := ui32_lt_2p32 a.1
          have hpow : 2 ^ 32 = 2 ^ (32 - s.1.toNat) * 2 ^ s.1.toNat := by
            rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk32n)]
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
          omega
        let q2 := a.2.toNat / 2 ^ s.1.toNat
        let r2 := a.2.toNat % 2 ^ s.1.toNat
        have ha2_eq : a.2.toNat = q2 * 2 ^ s.1.toNat + r2 := by
          dsimp only [q2, r2]
          rw [Nat.mul_comm]
          exact (Nat.div_add_mod a.2.toNat (2 ^ s.1.toNat)).symm
        have hor := ui32_or_disjoint_toNat ha1_lt ⟨r2, ha2_shl⟩
        unfold Nat64.toNat
        rw [hor, ha1_shr, ha2_shl, ha2_shr]
        have hpow32 : 2 ^ 32 = 2 ^ (32 - s.1.toNat) * 2 ^ s.1.toNat := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk32n)]
        have hnum : a.1.toNat + a.2.toNat * 2 ^ 32 =
            a.1.toNat + (r2 * 2 ^ (32 - s.1.toNat) + q2 * 2 ^ 32) * 2 ^ s.1.toNat := by
          calc a.1.toNat + a.2.toNat * 2 ^ 32
              = a.1.toNat + (q2 * 2 ^ s.1.toNat + r2) * 2 ^ 32 := by rw [ha2_eq]
            _ = a.1.toNat + (q2 * 2 ^ 32 * 2 ^ s.1.toNat + r2 * 2 ^ (32 - s.1.toNat) * 2 ^ s.1.toNat) := by
                rw [Nat.add_mul, Nat.mul_assoc q2, Nat.mul_comm (2 ^ s.1.toNat) (2 ^ 32), ← Nat.mul_assoc q2,
                  hpow32, ← Nat.mul_assoc r2]
            _ = a.1.toNat + (r2 * 2 ^ (32 - s.1.toNat) + q2 * 2 ^ 32) * 2 ^ s.1.toNat := by
                rw [Nat.add_comm (q2 * 2 ^ 32 * 2 ^ s.1.toNat), ← Nat.add_mul]
        rw [hnum, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide))]
        dsimp only [r2, q2]
        omega
      · simp only [hk32, ↓reduceIte]
        have hk32le : 32 ≤ s.1.toNat := by
          change ¬ s.1.toNat < (32 : UInt32).toNat at hk32; simp at hk32; omega
        by_cases hkeq : s.1 = 32
        · simp only [hkeq, beq_self_eq_true, ↓reduceIte]
          unfold Nat64.toNat
          have h32 : (32 : UInt32).toNat = 32 := rfl
          rw [h32, UInt32.toNat_zero, Nat.zero_mul, Nat.add_zero]
          rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
            Nat.div_eq_of_lt (ui32_lt_2p32 a.1), Nat.zero_add]
        · have hk32gt : 32 < s.1.toNat := by
            have hne : s.1.toNat ≠ 32 := fun hz => hkeq (ui32_eq_of_toNat_eq (by simpa using hz))
            omega
          have hbeq32 : (s.1 == 32) = false := beq_false_of_ne hkeq
          simp only [hbeq32, Bool.false_eq_true, ↓reduceIte]
          have hsub : (s.1 - 32).toNat = s.1.toNat - 32 :=
            ui32_sub_eq_of_le hk32le
          have hsub_lt : (s.1 - 32).toNat < 32 := by rw [hsub]; omega
          unfold Nat64.toNat
          rw [UInt32.toNat_zero, Nat.zero_mul, Nat.add_zero,
            ui32_shiftRight_toNat a.2 (s.1 - 32) hsub_lt, hsub]
          have hpow : 2 ^ s.1.toNat = 2 ^ 32 * 2 ^ (s.1.toNat - 32) := by
            rw [← Nat.pow_add, Nat.add_sub_of_le hk32le]
          rw [hpow, ← Nat.div_div_eq_div_mul,
            Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
            Nat.div_eq_of_lt (ui32_lt_2p32 a.1), Nat.zero_add]

/-- Exact 64-bit left shift returning `.delegate .intOverflow` whenever `a <<< s >= 2^64`.
    Never silently truncates overflowed bits. -/
def nat64ShlChecked (a s : Nat64) : MachineStatus Nat64 :=
  if nat64IsZero a then .ok (0, 0)
  else if s.2 != 0 || s.1 >= 64 then .delegate .intOverflow
  else
    let k := s.1
    if k == 0 then .ok a
    else if k < 32 then
      if (a.2 >>> (32 - k)) != 0 then .delegate .intOverflow
      else .ok (a.1 <<< k, (a.2 <<< k) ||| (a.1 >>> (32 - k)))
    else
      let k' := k - 32
      if a.2 != 0 then .delegate .intOverflow
      else if k' > 0 && (a.1 >>> (32 - k')) != 0 then .delegate .intOverflow
      else .ok (0, a.1 <<< k')

theorem nat64ShlChecked_correct (a s : Nat64) :
    (∀ r, nat64ShlChecked a s = .ok r ->
      r.toNat = a.toNat <<< s.toNat ∧ r.toNat < 2 ^ 64) ∧
    (2 ^ 64 ≤ a.toNat <<< s.toNat ->
      nat64ShlChecked a s = .delegate .intOverflow) ∧
    (a.toNat <<< s.toNat < 2 ^ 64 ->
      ∃ r, nat64ShlChecked a s = .ok r ∧ r.toNat = a.toNat <<< s.toNat) := by
  have hmain :
      if a.toNat <<< s.toNat < 2 ^ 64 then
        ∃ r, nat64ShlChecked a s = .ok r ∧ r.toNat = a.toNat <<< s.toNat
      else
        nat64ShlChecked a s = .delegate .intOverflow := by
    rw [Nat.shiftLeft_eq]
    by_cases haz : a.toNat = 0
    · have hza : nat64IsZero a = true := (nat64IsZero_iff a).mpr haz
      have hlt : a.toNat * 2 ^ s.toNat < 2 ^ 64 := by rw [haz]; simp
      simp only [hlt, ↓reduceIte]
      refine ⟨(0, 0), ?_, ?_⟩
      · unfold nat64ShlChecked; simp [hza]
      · rw [haz]; simp [Nat64.toNat]
    · have hapos : 0 < a.toNat := Nat.pos_of_ne_zero haz
      have hnz : nat64IsZero a = false := by
        cases h : nat64IsZero a
        · rfl
        · exfalso; exact haz ((nat64IsZero_iff a).mp h)
      by_cases hs64 : 64 ≤ s.toNat
      · have hge : ¬ a.toNat * 2 ^ s.toNat < 2 ^ 64 := by
          have hpow : 2 ^ 64 ≤ 2 ^ s.toNat := Nat.pow_le_pow_right (by decide) hs64
          have hmul : 2 ^ 64 ≤ a.toNat * 2 ^ s.toNat :=
            Nat.le_trans hpow (Nat.le_mul_of_pos_left _ hapos)
          omega
        simp only [hge, ↓reduceIte]
        have hcond : (s.2 != 0 || decide (64 ≤ s.1)) = true := by
          by_cases hs2 : s.2 = 0
          · have hs1 : 64 ≤ s.1.toNat := by
              unfold Nat64.toNat at hs64; rw [hs2] at hs64; simpa using hs64
            have hdec : decide ((64 : UInt32) ≤ s.1) = true := decide_eq_true hs1
            simp [hdec]
          · simp [hs2]
        unfold nat64ShlChecked
        simp [hnz, hcond]
      · have hs2 : s.2 = 0 := by
          by_cases hne : s.2 = 0
          · exact hne
          · have hpos : 1 ≤ s.2.toNat := by
              have hn0 : s.2.toNat ≠ 0 := fun hz => hne (ui32_eq_of_toNat_eq (by simpa using hz))
              omega
            unfold Nat64.toNat at hs64
            have : (2 ^ 32 : Nat) ≤ s.2.toNat * 2 ^ 32 := Nat.le_mul_of_pos_left _ hpos
            omega
        have hk64 : s.1.toNat < 64 := by
          unfold Nat64.toNat at hs64; rw [hs2] at hs64; simp at hs64; omega
        have hs_nat : s.toNat = s.1.toNat := by
          unfold Nat64.toNat; rw [hs2]; simp
        have hcond : (s.2 != 0 || decide (64 ≤ s.1)) = false := by
          simp only [hs2, bne_self_eq_false, Bool.false_or, decide_eq_false_iff_not]
          change ¬ 64 ≤ s.1.toNat; omega
        rw [hs_nat]
        by_cases hk0 : s.1 = 0
        · have hk0n : s.1.toNat = 0 := by rw [hk0]; rfl
          have hlt : a.toNat * 2 ^ s.1.toNat < 2 ^ 64 := by
            rw [hk0n]; simpa using nat64_toNat_lt a
          simp only [hlt, ↓reduceIte]
          refine ⟨a, ?_, ?_⟩
          · unfold nat64ShlChecked; simp [hnz, hs2, hk0]
          · rw [hk0n]; simp
        · have hk0n : s.1.toNat ≠ 0 := fun hz => hk0 (ui32_eq_of_toNat_eq (by simpa using hz))
          have hbeq0 : (s.1 == 0) = false := beq_false_of_ne hk0
          by_cases hk32 : s.1 < 32
          · have hk32n : s.1.toNat < 32 := hk32
            have hsub : (32 - s.1).toNat = 32 - s.1.toNat := by
              apply ui32_sub_eq_of_le; change s.1.toNat ≤ (32 : UInt32).toNat; simp; omega
            have hsub_lt : (32 - s.1).toNat < 32 := by rw [hsub]; omega
            have hhi : (a.2 >>> (32 - s.1)).toNat = a.2.toNat / 2 ^ (32 - s.1.toNat) := by
              rw [ui32_shiftRight_toNat a.2 (32 - s.1) hsub_lt, hsub]
            let q2 := a.2.toNat / 2 ^ (32 - s.1.toNat)
            let r2 := a.2.toNat % 2 ^ (32 - s.1.toNat)
            have ha2_eq : a.2.toNat = q2 * 2 ^ (32 - s.1.toNat) + r2 := by
              dsimp only [q2, r2]
              rw [Nat.mul_comm]
              exact (Nat.div_add_mod a.2.toNat (2 ^ (32 - s.1.toNat))).symm
            have hpow1 : 2 ^ (32 - s.1.toNat) * 2 ^ s.1.toNat = 2 ^ 32 := by
              rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk32n)]
            have hpow2 : 2 ^ 32 * 2 ^ s.1.toNat = 2 ^ (32 + s.1.toNat) := by rw [← Nat.pow_add]
            have hpow3 : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
            have hprod : a.toNat * 2 ^ s.1.toNat =
                a.1.toNat * 2 ^ s.1.toNat + r2 * 2 ^ (32 + s.1.toNat) + q2 * 2 ^ 64 := by
              unfold Nat64.toNat
              calc (a.1.toNat + a.2.toNat * 2 ^ 32) * 2 ^ s.1.toNat
                  = a.1.toNat * 2 ^ s.1.toNat + ((q2 * 2 ^ (32 - s.1.toNat) + r2) * 2 ^ 32) * 2 ^ s.1.toNat := by
                    rw [Nat.add_mul, ha2_eq]
                _ = a.1.toNat * 2 ^ s.1.toNat + (q2 * 2 ^ (32 - s.1.toNat) * 2 ^ s.1.toNat * 2 ^ 32 +
                      r2 * (2 ^ 32 * 2 ^ s.1.toNat)) := by
                    rw [Nat.add_mul, Nat.add_mul,
                      Nat.mul_right_comm (q2 * 2 ^ (32 - s.1.toNat)) (2 ^ 32) (2 ^ s.1.toNat),
                      Nat.mul_assoc r2 (2 ^ 32) (2 ^ s.1.toNat)]
                _ = a.1.toNat * 2 ^ s.1.toNat + r2 * 2 ^ (32 + s.1.toNat) + q2 * 2 ^ 64 := by
                    rw [Nat.mul_assoc q2 (2 ^ (32 - s.1.toNat)) (2 ^ s.1.toNat), hpow1,
                      Nat.mul_assoc q2 (2 ^ 32) (2 ^ 32), hpow3, hpow2]
                    omega
            by_cases hq2 : q2 = 0
            · have hr2_le : r2 ≤ 2 ^ (32 - s.1.toNat) - 1 := by
                have := Nat.mod_lt a.2.toNat (Nat.pow_pos (by decide) : 0 < 2 ^ (32 - s.1.toNat))
                change r2 < 2 ^ (32 - s.1.toNat) at this
                omega
              have ha1_le : a.1.toNat ≤ 2 ^ 32 - 1 := by
                have := ui32_lt_2p32 a.1; omega
              have hbound1 : r2 * 2 ^ (32 + s.1.toNat) ≤ (2 ^ (32 - s.1.toNat) - 1) * 2 ^ (32 + s.1.toNat) :=
                Nat.mul_le_mul_right _ hr2_le
              have hbound2 : a.1.toNat * 2 ^ s.1.toNat ≤ (2 ^ 32 - 1) * 2 ^ s.1.toNat :=
                Nat.mul_le_mul_right _ ha1_le
              have hsum_hi : (2 ^ (32 - s.1.toNat) - 1) * 2 ^ (32 + s.1.toNat) + 2 ^ (32 + s.1.toNat) = 2 ^ 64 := by
                have hpos : 0 < 2 ^ (32 - s.1.toNat) := Nat.pow_pos (by decide)
                rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add]
                have hexp : 32 - s.1.toNat + (32 + s.1.toNat) = 64 := by omega
                rw [hexp]
                have : 2 ^ (32 + s.1.toNat) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
                omega
              have hsum_lo : (2 ^ 32 - 1) * 2 ^ s.1.toNat + 2 ^ s.1.toNat = 2 ^ (32 + s.1.toNat) := by
                rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add]
                have : 2 ^ s.1.toNat ≤ 2 ^ (32 + s.1.toNat) := Nat.pow_le_pow_right (by decide) (by omega)
                omega
              have hlt : a.toNat * 2 ^ s.1.toNat < 2 ^ 64 := by
                rw [hprod, hq2, Nat.zero_mul, Nat.add_zero]
                have hpos : 0 < 2 ^ s.1.toNat := Nat.pow_pos (by decide)
                omega
              simp only [hlt, ↓reduceIte]
              have hhi0 : (a.2 >>> (32 - s.1)) = 0 := ui32_eq_of_toNat_eq (by rw [hhi]; exact hq2)
              refine ⟨(a.1 <<< s.1, (a.2 <<< s.1) ||| (a.1 >>> (32 - s.1))), ?_, ?_⟩
              · unfold nat64ShlChecked
                simp [hnz, hcond, hbeq0, hk32, hhi0]
              · unfold Nat64.toNat
                have ha1_shl : (a.1 <<< s.1).toNat =
                    (a.1.toNat % 2 ^ (32 - s.1.toNat)) * 2 ^ s.1.toNat :=
                  ui32_shiftLeft_low_mul hk32n
                have ha1_shr : (a.1 >>> (32 - s.1)).toNat = a.1.toNat / 2 ^ (32 - s.1.toNat) := by
                  rw [ui32_shiftRight_toNat a.1 (32 - s.1) hsub_lt, hsub]
                have ha1_shr_lt : (a.1 >>> (32 - s.1)).toNat < 2 ^ s.1.toNat := by
                  rw [ha1_shr, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
                  have ha1 : a.1.toNat < 2 ^ 32 := ui32_lt_2p32 a.1
                  have hpow : 2 ^ s.1.toNat * 2 ^ (32 - s.1.toNat) = 2 ^ 32 := by
                    rw [← Nat.pow_add]; congr 1; omega
                  omega
                have ha2_shl : (a.2 <<< s.1).toNat = r2 * 2 ^ s.1.toNat := by
                  rw [ui32_shiftLeft_low_mul hk32n]
                have hor : ((a.2 <<< s.1) ||| (a.1 >>> (32 - s.1))).toNat =
                    (a.1 >>> (32 - s.1)).toNat + (a.2 <<< s.1).toNat := by
                  rw [UInt32.or_comm]
                  exact ui32_or_disjoint_toNat ha1_shr_lt ⟨r2, ha2_shl⟩
                rw [hor, ha1_shl, ha2_shl, ha1_shr]
                let q1 := a.1.toNat / 2 ^ (32 - s.1.toNat)
                let r1 := a.1.toNat % 2 ^ (32 - s.1.toNat)
                have ha1_eq : a.1.toNat = q1 * 2 ^ (32 - s.1.toNat) + r1 := by
                  dsimp only [q1, r1]
                  rw [Nat.mul_comm]
                  exact (Nat.div_add_mod a.1.toNat (2 ^ (32 - s.1.toNat))).symm
                have hstep1 : (a.1.toNat + a.2.toNat * 2 ^ 32) * 2 ^ s.1.toNat =
                    a.1.toNat * 2 ^ s.1.toNat + r2 * 2 ^ (32 + s.1.toNat) := by
                  calc (a.1.toNat + a.2.toNat * 2 ^ 32) * 2 ^ s.1.toNat
                      = a.toNat * 2 ^ s.1.toNat := rfl
                    _ = a.1.toNat * 2 ^ s.1.toNat + r2 * 2 ^ (32 + s.1.toNat) + q2 * 2 ^ 64 := hprod
                    _ = a.1.toNat * 2 ^ s.1.toNat + r2 * 2 ^ (32 + s.1.toNat) := by rw [hq2, Nat.zero_mul, Nat.add_zero]
                rw [hstep1]
                calc r1 * 2 ^ s.1.toNat + (q1 + r2 * 2 ^ s.1.toNat) * 2 ^ 32
                    = r1 * 2 ^ s.1.toNat + q1 * (2 ^ (32 - s.1.toNat) * 2 ^ s.1.toNat) +
                        r2 * (2 ^ s.1.toNat * 2 ^ 32) := by
                      rw [Nat.add_mul, hpow1, Nat.mul_assoc r2]; omega
                  _ = (q1 * 2 ^ (32 - s.1.toNat) + r1) * 2 ^ s.1.toNat + r2 * 2 ^ (32 + s.1.toNat) := by
                      rw [Nat.add_mul, Nat.mul_assoc q1, Nat.mul_comm (2 ^ s.1.toNat) (2 ^ 32), hpow2]; omega
                  _ = a.1.toNat * 2 ^ s.1.toNat + r2 * 2 ^ (32 + s.1.toNat) := by
                      rw [← ha1_eq]
            · have hposq : 1 ≤ q2 := Nat.pos_of_ne_zero hq2
              have hge : ¬ a.toNat * 2 ^ s.1.toNat < 2 ^ 64 := by
                rw [hprod]
                have hqmul : 2 ^ 64 ≤ q2 * 2 ^ 64 := Nat.le_mul_of_pos_left _ hposq
                omega
              simp only [hge, ↓reduceIte]
              have hne0 : ((a.2 >>> (32 - s.1)) != 0) = true := by
                simp only [bne_iff_ne, ne_eq]
                intro hz
                have := congrArg UInt32.toNat hz
                rw [hhi, UInt32.toNat_zero] at this
                exact hq2 this
              unfold nat64ShlChecked
              simp [hnz, hcond, hbeq0, hk32, hne0]
          · have hk32le : 32 ≤ s.1.toNat := by
              change ¬ s.1.toNat < (32 : UInt32).toNat at hk32; simp at hk32; omega
            have hsub32 : (s.1 - 32).toNat = s.1.toNat - 32 := ui32_sub_eq_of_le hk32le
            have hsub32_lt : (s.1 - 32).toNat < 32 := by rw [hsub32]; omega
            by_cases ha2z : a.2 = 0
            · by_cases hkp0 : s.1 - 32 = 0
              · have hk32_eq : s.1.toNat = 32 := by
                  have : (s.1 - 32).toNat = 0 := by rw [hkp0]; rfl
                  omega
                have ha2n : a.2.toNat = 0 := by rw [ha2z]; rfl
                have hlt : a.toNat * 2 ^ s.1.toNat < 2 ^ 64 := by
                  unfold Nat64.toNat
                  rw [ha2n, hk32_eq, Nat.zero_mul, Nat.add_zero]
                  have ha1 : a.1.toNat < 2 ^ 32 := ui32_lt_2p32 a.1
                  have hpow : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
                  have hmul := Nat.mul_lt_mul_of_pos_right ha1 (Nat.pow_pos (by decide) : 0 < 2 ^ 32)
                  omega
                simp only [hlt, ↓reduceIte]
                refine ⟨(0, a.1 <<< (s.1 - 32)), ?_, ?_⟩
                · unfold nat64ShlChecked
                  simp [hnz, hcond, hbeq0, hk32, ha2z, hkp0]
                · unfold Nat64.toNat
                  rw [hkp0, UInt32.shiftLeft_zero, UInt32.toNat_zero, Nat.zero_add,
                    ha2n, Nat.zero_mul, Nat.add_zero, hk32_eq]
              · have hk'pos : 0 < (s.1 - 32).toNat := by
                  have : (s.1 - 32).toNat ≠ 0 := fun hz => hkp0 (ui32_eq_of_toNat_eq (by simpa using hz))
                  omega
                have hk'ui : (0 : UInt32) < s.1 - 32 := hk'pos
                have hsub' : (32 - (s.1 - 32)).toNat = 32 - (s.1 - 32).toNat := by
                  apply ui32_sub_eq_of_le
                  change (s.1 - 32).toNat ≤ (32 : UInt32).toNat; simp; omega
                have hsub'_lt : (32 - (s.1 - 32)).toNat < 32 := by rw [hsub']; omega
                have hhi1 : (a.1 >>> (32 - (s.1 - 32))).toNat =
                    a.1.toNat / 2 ^ (32 - (s.1 - 32).toNat) := by
                  rw [ui32_shiftRight_toNat a.1 (32 - (s.1 - 32)) hsub'_lt, hsub']
                let q1 := a.1.toNat / 2 ^ (32 - (s.1 - 32).toNat)
                let r1 := a.1.toNat % 2 ^ (32 - (s.1 - 32).toNat)
                have ha1_eq : a.1.toNat = q1 * 2 ^ (32 - (s.1 - 32).toNat) + r1 := by
                  dsimp only [q1, r1]
                  rw [Nat.mul_comm]
                  exact (Nat.div_add_mod a.1.toNat (2 ^ (32 - (s.1 - 32).toNat))).symm
                have hpow_s : 2 ^ s.1.toNat = 2 ^ (s.1 - 32).toNat * 2 ^ 32 := by
                  rw [← Nat.pow_add]; congr 1; omega
                have hpow_mix : 2 ^ (32 - (s.1 - 32).toNat) * 2 ^ (s.1 - 32).toNat = 2 ^ 32 := by
                  rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hsub32_lt)]
                have ha2n : a.2.toNat = 0 := by rw [ha2z]; rfl
                have hpow3 : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
                have hprod' : a.toNat * 2 ^ s.1.toNat =
                    r1 * 2 ^ (32 + (s.1 - 32).toNat) + q1 * 2 ^ 64 := by
                  unfold Nat64.toNat
                  calc (a.1.toNat + a.2.toNat * 2 ^ 32) * 2 ^ s.1.toNat
                      = (q1 * 2 ^ (32 - (s.1 - 32).toNat) + r1) * (2 ^ (s.1 - 32).toNat * 2 ^ 32) := by
                        rw [ha2n, Nat.zero_mul, Nat.add_zero, ha1_eq, hpow_s]
                    _ = q1 * (2 ^ (32 - (s.1 - 32).toNat) * 2 ^ (s.1 - 32).toNat) * 2 ^ 32 +
                          r1 * (2 ^ 32 * 2 ^ (s.1 - 32).toNat) := by
                        rw [Nat.add_mul, Nat.mul_assoc q1, ← Nat.mul_assoc (2 ^ (32 - (s.1 - 32).toNat)),
                          ← Nat.mul_assoc q1, Nat.mul_comm (2 ^ (s.1 - 32).toNat) (2 ^ 32)]
                    _ = r1 * 2 ^ (32 + (s.1 - 32).toNat) + q1 * 2 ^ 64 := by
                        rw [hpow_mix, Nat.mul_assoc q1 (2 ^ 32) (2 ^ 32), hpow3, ← Nat.pow_add, Nat.add_comm]
                by_cases hq1 : q1 = 0
                · have ha1_lt_sub : a.1.toNat < 2 ^ (32 - (s.1 - 32).toNat) := by
                    rw [ha1_eq, hq1, Nat.zero_mul, Nat.zero_add]
                    exact Nat.mod_lt _ (Nat.pow_pos (by decide))
                  have hlt : a.toNat * 2 ^ s.1.toNat < 2 ^ 64 := by
                    rw [hprod', hq1, Nat.zero_mul, Nat.add_zero]
                    have hr1lt : r1 < 2 ^ (32 - (s.1 - 32).toNat) :=
                      Nat.mod_lt _ (Nat.pow_pos (by decide))
                    have hexp : 32 - (s.1 - 32).toNat + (32 + (s.1 - 32).toNat) = 64 := by omega
                    have hmul := Nat.mul_lt_mul_of_pos_right hr1lt
                      (Nat.pow_pos (by decide) : 0 < 2 ^ (32 + (s.1 - 32).toNat))
                    rw [← Nat.pow_add, hexp] at hmul
                    exact hmul
                  simp only [hlt, ↓reduceIte]
                  have hhi1z : a.1 >>> (32 - (s.1 - 32)) = 0 :=
                    ui32_eq_of_toNat_eq (by rw [hhi1]; exact hq1)
                  refine ⟨(0, a.1 <<< (s.1 - 32)), ?_, ?_⟩
                  · unfold nat64ShlChecked
                    simp [hnz, hcond, hbeq0, hk32, ha2z, hhi1z]
                  · unfold Nat64.toNat
                    have ha1_shl : (a.1 <<< (s.1 - 32)).toNat = a.1.toNat * 2 ^ (s.1 - 32).toNat := by
                      rw [ui32_shiftLeft_low_mul hsub32_lt, Nat.mod_eq_of_lt ha1_lt_sub]
                    rw [UInt32.toNat_zero, Nat.zero_add, ha1_shl, ha2n, Nat.zero_mul, Nat.add_zero,
                      hpow_s, Nat.mul_assoc]
                · have hposq : 1 ≤ q1 := Nat.pos_of_ne_zero hq1
                  have hge : ¬ a.toNat * 2 ^ s.1.toNat < 2 ^ 64 := by
                    rw [hprod']
                    have hqmul : 2 ^ 64 ≤ q1 * 2 ^ 64 := Nat.le_mul_of_pos_left _ hposq
                    omega
                  simp only [hge, ↓reduceIte]
                  have hne0 : ((a.1 >>> (32 - (s.1 - 32))) != 0) = true := by
                    simp only [bne_iff_ne, ne_eq]
                    intro hz
                    have := congrArg UInt32.toNat hz
                    rw [hhi1, UInt32.toNat_zero] at this
                    exact hq1 this
                  unfold nat64ShlChecked
                  simp [hnz, hcond, hbeq0, hk32, ha2z, hk'ui, hne0]
            · have ha2pos : 1 ≤ a.2.toNat := by
                have hz : a.2.toNat ≠ 0 := fun h0 => ha2z (ui32_eq_of_toNat_eq (by simpa using h0))
                omega
              have hge : ¬ a.toNat * 2 ^ s.1.toNat < 2 ^ 64 := by
                have hpow1 : 2 ^ 32 ≤ 2 ^ s.1.toNat := Nat.pow_le_pow_right (by decide) hk32le
                have h32 : 2 ^ 32 ≤ a.toNat := by
                  unfold Nat64.toNat
                  have : 2 ^ 32 ≤ a.2.toNat * 2 ^ 32 := Nat.le_mul_of_pos_left _ ha2pos
                  omega
                have hmul : 2 ^ 32 * 2 ^ 32 ≤ a.toNat * 2 ^ s.1.toNat := Nat.mul_le_mul h32 hpow1
                have hpow3 : (2 ^ 32 : Nat) * 2 ^ 32 = 2 ^ 64 := by decide
                omega
              simp only [hge, ↓reduceIte]
              unfold nat64ShlChecked
              simp [hnz, hcond, hbeq0, hk32, ha2z]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    by_cases hlt : a.toNat <<< s.toNat < 2 ^ 64
    · simp only [hlt, ↓reduceIte] at hmain
      rcases hmain with ⟨r', hr', hval⟩
      rw [hr] at hr'
      cases hr'
      exact ⟨hval, nat64_toNat_lt r⟩
    · simp only [hlt, ↓reduceIte] at hmain
      rw [hr] at hmain
      cases hmain
  · intro hge
    have hnot : ¬ a.toNat <<< s.toNat < 2 ^ 64 := by omega
    simp only [hnot, ↓reduceIte] at hmain
    exact hmain
  · intro hlt
    simp only [hlt, ↓reduceIte] at hmain
    exact hmain

/-- Shift a `Nat64` left by 1 bit and feed `bit` into bit 0, returning `(carryOut64, low64)`. -/
def nat64Shl1Add (x : Nat64) (bit : Bool) : Bool × Nat64 :=
  let carry : Bool := (x.2 >>> 31) != 0
  let b : UInt32 := if bit then 1 else 0
  let lo' : UInt32 := (x.1 <<< 1) ||| b
  let hi' : UInt32 := (x.2 <<< 1) ||| (x.1 >>> 31)
  (carry, (lo', hi'))

theorem nat64Shl1Add_correct (x : Nat64) (bit : Bool) :
    (if (nat64Shl1Add x bit).1 then 2 ^ 64 else 0) + (nat64Shl1Add x bit).2.toNat =
      2 * x.toNat + (if bit then 1 else 0) := by
  unfold nat64Shl1Add
  dsimp only
  have h1lt : (1 : UInt32).toNat < 32 := by decide
  have h31lt : (31 : UInt32).toNat < 32 := by decide
  have hlo_shl : (x.1 <<< 1).toNat = (x.1.toNat % 2 ^ 31) * 2 := by
    rw [ui32_shiftLeft_low_mul h1lt]; rfl
  have hhi_shl : (x.2 <<< 1).toNat = (x.2.toNat % 2 ^ 31) * 2 := by
    rw [ui32_shiftLeft_low_mul h1lt]; rfl
  have h1shr : (x.1 >>> 31).toNat = x.1.toNat / 2 ^ 31 :=
    ui32_shiftRight_toNat x.1 31 h31lt
  have h2shr : (x.2 >>> 31).toNat = x.2.toNat / 2 ^ 31 :=
    ui32_shiftRight_toNat x.2 31 h31lt
  have hx1_lt : x.1.toNat < 2 ^ 32 := ui32_lt_2p32 x.1
  have hx2_lt : x.2.toNat < 2 ^ 32 := ui32_lt_2p32 x.2
  have hb_lt : (if bit then (1 : UInt32) else 0).toNat < 2 ^ 1 := by
    cases bit <;> simp
  have hx1shr_lt : (x.1 >>> 31).toNat < 2 ^ 1 := by rw [h1shr]; omega
  have hlo : ((x.1 <<< 1) ||| (if bit then 1 else 0)).toNat =
      (if bit then 1 else 0) + (x.1.toNat % 2 ^ 31) * 2 := by
    rw [UInt32.or_comm]
    have hor := ui32_or_disjoint_toNat hb_lt ⟨x.1.toNat % 2 ^ 31, hlo_shl⟩
    rw [hor, hlo_shl]
    cases bit <;> simp
  have hhi : ((x.2 <<< 1) ||| (x.1 >>> 31)).toNat =
      x.1.toNat / 2 ^ 31 + (x.2.toNat % 2 ^ 31) * 2 := by
    rw [UInt32.or_comm]
    have hor := ui32_or_disjoint_toNat hx1shr_lt ⟨x.2.toNat % 2 ^ 31, hhi_shl⟩
    rw [hor, hhi_shl, h1shr]
  have hcarry : (if ((x.2 >>> 31) != 0) then (2 ^ 64 : Nat) else 0) =
      (x.2.toNat / 2 ^ 31) * 2 ^ 64 := by
    have hdiv2 : x.2.toNat / 2 ^ 31 = 0 ∨ x.2.toNat / 2 ^ 31 = 1 := by omega
    by_cases hc : x.2 >>> 31 = 0
    · have hc0 : x.2.toNat / 2 ^ 31 = 0 := by
        have := congrArg UInt32.toNat hc
        rw [h2shr, UInt32.toNat_zero] at this; exact this
      simp [hc, hc0]
    · have hne0 : ((x.2 >>> 31) != 0) = true := bne_iff_ne.mpr hc
      have hc1 : x.2.toNat / 2 ^ 31 = 1 := by
        rcases hdiv2 with h0 | h1
        · exfalso; apply hc; exact ui32_eq_of_toNat_eq (by rw [h2shr, h0]; rfl)
        · exact h1
      simp only [hne0, ↓reduceIte, hc1, Nat.one_mul]
  unfold Nat64.toNat
  rw [hcarry, hlo, hhi]
  have hx1_eq : x.1.toNat = (x.1.toNat / 2 ^ 31) * 2 ^ 31 + x.1.toNat % 2 ^ 31 := by
    have := Nat.div_add_mod x.1.toNat (2 ^ 31); omega
  have hx2_eq : x.2.toNat = (x.2.toNat / 2 ^ 31) * 2 ^ 31 + x.2.toNat % 2 ^ 31 := by
    have := Nat.div_add_mod x.2.toNat (2 ^ 31); omega
  have h2p31 : (2 * 2 ^ 31 : Nat) = 2 ^ 32 := by decide
  have h2p63 : (2 * (2 ^ 31 * 2 ^ 32) : Nat) = 2 ^ 64 := by decide
  omega

/-- Extract bit `k` (`0 <= k < 64`) of a `Nat64` limb pair. -/
def nat64Bit (a : Nat64) (k : Nat) : Bool :=
  if k < 32 then ((a.1 >>> UInt32.ofNat k) &&& 1) != 0
  else if k < 64 then ((a.2 >>> UInt32.ofNat (k - 32)) &&& 1) != 0
  else false

theorem nat64Bit_correct (a : Nat64) {k : Nat} (hk : k < 64) :
    (if nat64Bit a k then 1 else 0) = (a.toNat / 2 ^ k) % 2 := by
  have mod2_bit (x : UInt32) : (if ((x &&& 1) != 0) then 1 else 0) = x.toNat % 2 := by
    have hand : (x &&& 1).toNat = x.toNat % 2 := by
      rw [UInt32.toNat_and, UInt32.toNat_one]
      exact Nat.and_one_is_mod x.toNat
    by_cases h : x &&& 1 = 0
    · have hz : x.toNat % 2 = 0 := by
        have := congrArg UInt32.toNat h; rw [hand, UInt32.toNat_zero] at this; exact this
      simp [h, hz]
    · have h1 : x.toNat % 2 = 1 := by
        have hne : x.toNat % 2 ≠ 0 := fun hz => h (ui32_eq_of_toNat_eq (by rw [hand, hz]; rfl))
        omega
      have hne : (x &&& 1 != 0) = true := bne_iff_ne.mpr h
      simp only [hne, ↓reduceIte, h1]
  unfold nat64Bit
  by_cases hk32 : k < 32
  · simp only [hk32, ↓reduceIte, mod2_bit]
    have hkn : (UInt32.ofNat k).toNat = k := by
      change k % 2 ^ 32 = k
      exact Nat.mod_eq_of_lt (by omega)
    have hlt32 : (UInt32.ofNat k).toNat < 32 := by rw [hkn]; exact hk32
    rw [ui32_shiftRight_toNat a.1 (UInt32.ofNat k) hlt32, hkn]
    unfold Nat64.toNat
    have hpow : 2 ^ 32 = 2 ^ (32 - k) * 2 ^ k := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk32)]
    rw [hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide))]
    have h2sub : 2 ^ (32 - k) = 2 ^ (32 - k - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [h2sub, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  · simp only [hk32, ↓reduceIte, hk, mod2_bit]
    have hkn : (UInt32.ofNat (k - 32)).toNat = k - 32 := by
      change (k - 32) % 2 ^ 32 = k - 32
      exact Nat.mod_eq_of_lt (by omega)
    have hlt32 : (UInt32.ofNat (k - 32)).toNat < 32 := by rw [hkn]; omega
    rw [ui32_shiftRight_toNat a.2 (UInt32.ofNat (k - 32)) hlt32, hkn]
    unfold Nat64.toNat
    have hpow : 2 ^ k = 2 ^ 32 * 2 ^ (k - 32) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_not_lt hk32)]
    rw [hpow, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
      Nat.div_eq_of_lt (ui32_lt_2p32 a.1), Nat.zero_add]

private theorem nat64Shl1Add_lt_2p63_exact {q : Nat64} (hq : q.toNat < 2 ^ 63) (qb : Bool) :
    (nat64Shl1Add q qb).2.toNat = 2 * q.toNat + (if qb then 1 else 0) := by
  let qbNat : Nat := if qb then 1 else 0
  have hqb2 : qbNat < 2 := by cases qb <;> decide
  have hsq : (if (nat64Shl1Add q qb).1 then 2 ^ 64 else 0) + (nat64Shl1Add q qb).2.toNat =
      2 * q.toNat + qbNat := nat64Shl1Add_correct q qb
  have h264 : 2 * 2 ^ 63 = 2 ^ 64 := by rw [Nat.mul_comm, ← Nat.pow_succ]
  have hmul : 2 * q.toNat + 2 ≤ 2 ^ 64 := by
    have hq1 : q.toNat + 1 ≤ 2 ^ 63 := hq
    have h2 := Nat.mul_le_mul_left 2 hq1
    rw [Nat.mul_add, Nat.mul_one, h264] at h2
    exact h2
  have hlt64 : 2 * q.toNat + qbNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hqb2 (2 * q.toNat)) hmul
  cases hcf : (nat64Shl1Add q qb).1
  · rw [hcf] at hsq
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hsq
    exact hsq
  · rw [hcf] at hsq
    simp only [↓reduceIte] at hsq
    have hge64 : 2 ^ 64 ≤ 2 * q.toNat + qbNat := by
      rw [← hsq]; exact Nat.le_add_right _ _
    exact absurd (Nat.lt_of_le_of_lt hge64 hlt64) (Nat.lt_irrefl _)

/-- Single restoring binary division step updating `(q, r)`. -/
def nat64DivStep (b q r : Nat64) (bit : Bool) : Nat64 × Nat64 :=
  let sr := nat64Shl1Add r bit
  let carry := sr.1
  let r1 := sr.2
  if carry || !(nat64Lt r1 b) then
    ((nat64Shl1Add q true).2, nat64SubWrap r1 b)
  else
    ((nat64Shl1Add q false).2, r1)

private theorem nat64DivStep_ge_rem {b r : Nat64} {bit : Bool}
    (hr : r.toNat < b.toNat)
    (hge : ((nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)) = true) :
    (nat64SubWrap (nat64Shl1Add r bit).2 b).toNat =
      2 * r.toNat + (if bit then 1 else 0) - b.toNat ∧
    b.toNat ≤ 2 * r.toNat + (if bit then 1 else 0) := by
  have hbit2 : (if bit then 1 else 0) < 2 := by cases bit <;> decide
  have h2b : 2 * r.toNat + (if bit then 1 else 0) < 2 * b.toNat := by
    have hmul : 2 * r.toNat + 2 ≤ 2 * b.toNat := by
      have hr1 := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hr)
      rw [Nat.mul_succ] at hr1
      exact hr1
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hbit2 (2 * r.toNat)) hmul
  have hsr := nat64Shl1Add_correct r bit
  cases hc : (nat64Shl1Add r bit).1
  · rw [hc] at hge hsr
    simp only [Bool.false_or, Bool.not_eq_true'] at hge
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hsr
    have hle : b.toNat ≤ (nat64Shl1Add r bit).2.toNat := by
      cases hltb : nat64Lt (nat64Shl1Add r bit).2 b
      · apply Nat.le_of_not_lt
        intro hlt
        have ht := (nat64Lt_iff (nat64Shl1Add r bit).2 b).mpr hlt
        rw [hltb] at ht
        cases ht
      · rw [hltb] at hge; cases hge
    have hsub := nat64SubWrap_correct_of_ge hle
    exact ⟨by rw [hsub, hsr], by rw [← hsr]; exact hle⟩
  · rw [hc] at hsr
    simp only [↓reduceIte] at hsr
    have hb64 : b.toNat < 2 ^ 64 := nat64_toNat_lt b
    have hsum_lt : 2 ^ 64 + (nat64Shl1Add r bit).2.toNat < 2 ^ 64 + b.toNat := by
      have h2blt : 2 * b.toNat < 2 ^ 64 + b.toNat := by
        rw [Nat.two_mul]
        exact Nat.add_lt_add_right hb64 b.toNat
      rw [hsr]
      exact Nat.lt_trans h2b h2blt
    have hsr2_lt : (nat64Shl1Add r bit).2.toNat < b.toNat :=
      Nat.lt_of_add_lt_add_left hsum_lt
    have hsub := nat64SubWrap_correct_of_lt_borrow hsr2_lt
    have hb_le : b.toNat ≤ 2 * r.toNat + (if bit then 1 else 0) :=
      Nat.le_trans (Nat.le_of_lt hb64) (by rw [← hsr]; exact Nat.le_add_right _ _)
    exact ⟨by rw [hsub, hsr], hb_le⟩

private theorem nat64DivStep_true_eq (b q r : Nat64) (bit : Bool)
    (h : ((nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)) = true) :
    nat64DivStep b q r bit = ((nat64Shl1Add q true).2, nat64SubWrap (nat64Shl1Add r bit).2 b) := by
  unfold nat64DivStep
  dsimp only
  rw [h]
  simp only [↓reduceIte]

private theorem nat64DivStep_false_eq (b q r : Nat64) (bit : Bool)
    (h : ((nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)) = false) :
    nat64DivStep b q r bit = ((nat64Shl1Add q false).2, (nat64Shl1Add r bit).2) := by
  unfold nat64DivStep
  dsimp only
  rw [h]
  simp only [Bool.false_eq_true, ↓reduceIte]

private theorem nat64DivStep_true_branch {b q r : Nat64} {bit : Bool}
    (hr : r.toNat < b.toNat) (hq : q.toNat < 2 ^ 63)
    (hge : ((nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)) = true) :
    let qr' := ((nat64Shl1Add q true).2, nat64SubWrap (nat64Shl1Add r bit).2 b)
    qr'.1.toNat * b.toNat + qr'.2.toNat =
      2 * (q.toNat * b.toNat + r.toNat) + (if bit then 1 else 0) ∧
    qr'.2.toNat < b.toNat := by
  dsimp only
  have hbit2 : (if bit then 1 else 0) < 2 := by cases bit <;> decide
  have h2b : 2 * r.toNat + (if bit then 1 else 0) < 2 * b.toNat := by
    have hmul : 2 * r.toNat + 2 ≤ 2 * b.toNat := by
      have hr1 := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hr)
      rw [Nat.mul_succ] at hr1
      exact hr1
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hbit2 (2 * r.toNat)) hmul
  have hq' := nat64Shl1Add_lt_2p63_exact hq true
  simp only [↓reduceIte] at hq'
  have hr' := nat64DivStep_ge_rem hr hge
  constructor
  · rw [hq', hr'.1, Nat.add_mul, Nat.one_mul, Nat.mul_assoc 2 q.toNat b.toNat]
    rw [Nat.add_assoc (2 * (q.toNat * b.toNat)) b.toNat _]
    rw [Nat.add_sub_cancel' hr'.2]
    rw [← Nat.add_assoc (2 * (q.toNat * b.toNat)) (2 * r.toNat) _, ← Nat.mul_add]
  · rw [hr'.1]
    exact Nat.sub_lt_left_of_lt_add hr'.2 (by rw [← Nat.two_mul]; exact h2b)

private theorem nat64DivStep_false_cf {b r : Nat64} {bit : Bool}
    (hge : ((nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)) = false) :
    (nat64Shl1Add r bit).1 = false := by
  cases hc : (nat64Shl1Add r bit).1
  · rfl
  · rw [hc, Bool.true_or] at hge; cases hge

private theorem nat64DivStep_false_lt {b r : Nat64} {bit : Bool}
    (hge : ((nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)) = false) :
    nat64Lt (nat64Shl1Add r bit).2 b = true := by
  have hcf := nat64DivStep_false_cf hge
  rw [hcf, Bool.false_or] at hge
  cases hn : nat64Lt (nat64Shl1Add r bit).2 b
  · rw [hn] at hge; cases hge
  · rfl

private theorem nat64DivStep_false_branch {b q r : Nat64} {bit : Bool}
    (hq : q.toNat < 2 ^ 63)
    (hge : ((nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)) = false) :
    let qr' := ((nat64Shl1Add q false).2, (nat64Shl1Add r bit).2)
    qr'.1.toNat * b.toNat + qr'.2.toNat =
      2 * (q.toNat * b.toNat + r.toNat) + (if bit then 1 else 0) ∧
    qr'.2.toNat < b.toNat := by
  dsimp only
  have hcf := nat64DivStep_false_cf hge
  have hltb := nat64DivStep_false_lt hge
  have hlt_nat : (nat64Shl1Add r bit).2.toNat < b.toNat := (nat64Lt_iff _ b).mp hltb
  have hsr := nat64Shl1Add_correct r bit
  rw [hcf] at hsr
  have hite0 : (if false = true then 2 ^ 64 else 0) = 0 := by
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hite0, Nat.zero_add] at hsr
  have hq' := nat64Shl1Add_lt_2p63_exact hq false
  have hite1 : (if false = true then (1 : Nat) else 0) = 0 := by
    simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hite1, Nat.add_zero] at hq'
  constructor
  · rw [hq', hsr, Nat.mul_assoc 2 q.toNat b.toNat]
    rw [← Nat.add_assoc (2 * (q.toNat * b.toNat)) (2 * r.toNat) _, ← Nat.mul_add]
  · exact hlt_nat

theorem nat64DivStep_inv {b q r : Nat64} {bit : Bool}
    (hb : 0 < b.toNat) (hr : r.toNat < b.toNat) (hq : q.toNat < 2 ^ 63) :
    let qr' := nat64DivStep b q r bit
    qr'.1.toNat * b.toNat + qr'.2.toNat =
      2 * (q.toNat * b.toNat + r.toNat) + (if bit then 1 else 0) ∧
    qr'.2.toNat < b.toNat := by
  have _ := hb
  dsimp only
  cases hge : (nat64Shl1Add r bit).1 || !(nat64Lt (nat64Shl1Add r bit).2 b)
  · rw [nat64DivStep_false_eq b q r bit hge]
    exact nat64DivStep_false_branch hq hge
  · rw [nat64DivStep_true_eq b q r bit hge]
    exact nat64DivStep_true_branch hr hq hge

/-- Structural 64-step restoring binary long-division loop over bit indices `63` down to `0`. -/
def nat64DivLoop (a b : Nat64) : Nat -> Nat64 -> Nat64 -> Nat64 × Nat64
  | 0, q, r => (q, r)
  | k + 1, q, r =>
    let qr' := nat64DivStep b q r (nat64Bit a k)
    nat64DivLoop a b k qr'.1 qr'.2

theorem nat64DivLoop_inv (a b : Nat64) (hb : 0 < b.toNat) :
    ∀ (k : Nat), k ≤ 64 -> ∀ (q r : Nat64),
      q.toNat * b.toNat + r.toNat = a.toNat / 2 ^ k ->
      r.toNat < b.toNat ->
      let res := nat64DivLoop a b k q r
      res.1.toNat * b.toNat + res.2.toNat = a.toNat ∧ res.2.toNat < b.toNat
  | 0, _, q, r, hinv, hr => by
    simp only [nat64DivLoop]
    rw [Nat.pow_zero, Nat.div_one] at hinv
    exact ⟨hinv, hr⟩
  | k + 1, hk, q, r, hinv, hr => by
    simp only [nat64DivLoop]
    have ha64 : a.toNat < 2 ^ 64 := nat64_toNat_lt a
    have hpow64 : 2 ^ 64 = 2 ^ (64 - (k + 1)) * 2 ^ (k + 1) := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hk]
    have hbound_div : a.toNat / 2 ^ (k + 1) < 2 ^ (64 - (k + 1)) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]; omega
    have hpow63 : 2 ^ (64 - (k + 1)) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have hq63 : q.toNat < 2 ^ 63 := by
      have : q.toNat ≤ q.toNat * b.toNat + r.toNat := by
        have := Nat.le_mul_of_pos_right q.toNat hb; omega
      omega
    have hstep := nat64DivStep_inv (bit := nat64Bit a k) hb hr hq63
    have hbit := nat64Bit_correct a (k := k) (by omega)
    have hdiv_step : a.toNat / 2 ^ k = 2 * (a.toNat / 2 ^ (k + 1)) + (a.toNat / 2 ^ k) % 2 := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      have := Nat.div_add_mod (a.toNat / 2 ^ k) 2
      omega
    have hinv' : (nat64DivStep b q r (nat64Bit a k)).1.toNat * b.toNat +
        (nat64DivStep b q r (nat64Bit a k)).2.toNat = a.toNat / 2 ^ k := by
      rw [hstep.1, hinv, hbit, ← hdiv_step]
    exact nat64DivLoop_inv a b hb k (by omega) _ _ hinv' hstep.2

/-- Exact 64-bit limb-pair Euclidean division (`((0, 0), a)` when `b == 0`). -/
def nat64DivMod (a b : Nat64) : Nat64 × Nat64 :=
  if nat64IsZero b then ((0, 0), a)
  else nat64DivLoop a b 64 (0, 0) (0, 0)

def nat64Div (a b : Nat64) : Nat64 := (nat64DivMod a b).1
def nat64Mod (a b : Nat64) : Nat64 := (nat64DivMod a b).2

theorem nat64DivMod_spec (a b : Nat64) :
    if b.toNat = 0 then (nat64Div a b).toNat = 0 ∧ (nat64Mod a b).toNat = a.toNat
    else (nat64Div a b).toNat = a.toNat / b.toNat ∧ (nat64Mod a b).toNat = a.toNat % b.toNat := by
  unfold nat64Div nat64Mod nat64DivMod
  by_cases hbz : b.toNat = 0
  · have htb : nat64IsZero b = true := (nat64IsZero_iff b).mpr hbz
    simp only [hbz, htb, ↓reduceIte]
    simp [Nat64.toNat]
  · have hfb : nat64IsZero b = false := by
      cases h : nat64IsZero b
      · rfl
      · exfalso; exact hbz ((nat64IsZero_iff b).mp h)
    simp only [hbz, hfb, Bool.false_eq_true, ↓reduceIte]
    have hbpos : 0 < b.toNat := Nat.pos_of_ne_zero hbz
    have hinit_inv : nat64Zero.toNat * b.toNat + nat64Zero.toNat = a.toNat / 2 ^ 64 := by
      rw [Nat.div_eq_of_lt (nat64_toNat_lt a), nat64Zero_toNat, Nat.zero_mul, Nat.zero_add]
    have hinit_r : nat64Zero.toNat < b.toNat := by simpa [nat64Zero, Nat64.toNat] using hbpos
    have hres := nat64DivLoop_inv a b hbpos 64 (Nat.le_refl 64) nat64Zero nat64Zero hinit_inv hinit_r
    let q : Nat64 := (nat64DivLoop a b 64 (0, 0) (0, 0)).1
    let r : Nat64 := (nat64DivLoop a b 64 (0, 0) (0, 0)).2
    have hres' : q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat := hres
    have haeq : a.toNat = r.toNat + b.toNat * q.toNat := by
      rw [Nat.mul_comm b.toNat q.toNat]; omega
    have hq_eq : q.toNat = a.toNat / b.toNat := by
      have : (r.toNat + b.toNat * q.toNat) / b.toNat = q.toNat := by
        rw [Nat.add_mul_div_left _ _ hbpos, Nat.div_eq_of_lt hres'.2, Nat.zero_add]
      rw [← haeq] at this
      exact this.symm
    have hr_eq : r.toNat = a.toNat % b.toNat := by
      have : (r.toNat + b.toNat * q.toNat) % b.toNat = r.toNat := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hres'.2]
      rw [← haeq] at this
      exact this.symm
    exact ⟨hq_eq, hr_eq⟩

theorem nat64Div_correct (a b : Nat64) :
    (nat64Div a b).toNat = if b.toNat = 0 then 0 else a.toNat / b.toNat := by
  have h := nat64DivMod_spec a b
  split
  · next hbz => simp only [hbz, ↓reduceIte] at h; exact h.1
  · next hnz => simp only [hnz, ↓reduceIte] at h; exact h.1

theorem nat64Mod_correct (a b : Nat64) :
    (nat64Mod a b).toNat = if b.toNat = 0 then a.toNat else a.toNat % b.toNat := by
  have h := nat64DivMod_spec a b
  split
  · next hbz => simp only [hbz, ↓reduceIte] at h; exact h.2
  · next hnz => simp only [hnz, ↓reduceIte] at h; exact h.2

end ConGpuProof
