/-
ConGpuProof.StepMachine
=======================
Formal specification and soundness proof for con-gpu's bounded-frame,
stackless iterative GPU typechecker state machine (`Frame`, `KontStack`,
`MachineStatus`, `step`, `runSteps`) over the two-tier SoA expression arena.

Proves:
  * `delegate_never_accepts` : resource-exhausted GPU threads never return `.ok`.
  * `stepMachine_sound`      : every `.ok ty` terminal result decodes to a type
    validated by the declarative recursive kernel specification `inferSpec`
    (and `HasType`).
-/

import ConGpuProof.ArenaOps

namespace ConGpuProof

/-! ### 1. Frames, Continuation Stack, Control Register, and Machine State -/

/-- Explicit stackless continuation frames for iterative WHNF, DefEq, and Infer. -/
inductive Frame where
  | appFn (ctx : List EIdx) (arg : EIdx)
  | appWhnf (ctx : List EIdx) (arg : EIdx)
  | appArg (ctx : List EIdx) (dom cod arg : EIdx)
  | appDefEq (cod arg : EIdx)
  | lamDom (ctx : List EIdx) (dom body : EIdx)
  | lamDomWhnf (ctx : List EIdx) (dom body : EIdx)
  | lamBody (fid : Nat) (dom : EIdx)
  | forallDom (ctx : List EIdx) (dom body : EIdx)
  | forallDomWhnf (ctx : List EIdx) (dom body : EIdx)
  | forallBody (u : UInt32)
  | forallBodyWhnf (u : UInt32)
  | letTy (ctx : List EIdx) (ty val body : EIdx)
  | letTyWhnf (ctx : List EIdx) (ty val body : EIdx)
  | letVal (ctx : List EIdx) (ty val body : EIdx)
  | letValDefEq (ctx : List EIdx) (ty val body : EIdx)
  | letBody (fid : Nat) (ty val : EIdx)
  | whnfApp (arg : EIdx)
  | defEqLhs (fid : Nat) (b : EIdx)
  | defEqRhs (fid : Nat) (wa : EIdx)
  | defEqSecond (fid : Nat) (e₁ e₂ : EIdx)
  deriving DecidableEq, Repr, Inhabited

/-- Bounded continuation stack manipulated by `step`. -/
abbrev KontStack := List Frame

/-- Control register selecting the active phase or return value. -/
inductive Control where
  | evalInfer (ctx : List EIdx) (e : EIdx)
  | evalWhnf (e : EIdx)
  | evalDefEq (fid : Nat) (a b : EIdx)
  | retInfer (ty : EIdx)
  | retWhnf (w : EIdx)
  | retDefEq (ok : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Complete per-thread state of the stackless iterative GPU typechecker. -/
structure MachineState where
  cfg : MachineLimits
  pers : SoATier
  scr : SoATier
  gpuEnv : Array GpuConstDecl
  ctrl : Control
  stack : KontStack
  stepsUsed : Nat
  status : MachineStatus EIdx
  deriving Repr, Inhabited

/-- Initialize type inference for expression handle `e` with empty context and scratch tier. -/
def initInfer (cfg : MachineLimits) (gpuEnv : Array GpuConstDecl)
    (pers : SoATier) (e : EIdx) : MachineState :=
  { cfg := cfg
    pers := pers
    scr := .empty
    gpuEnv := gpuEnv
    ctrl := .evalInfer [] e
    stack := []
    stepsUsed := 0
    status := .running }

/-! ### 2. Single-Step State Machine Transition (`step`) & Bounded Execution -/

private def goCtrl (s : MachineState) (scr' : SoATier) (c : Control) : MachineState :=
  { s with scr := scr', ctrl := c, stepsUsed := s.stepsUsed + 1, status := .running }

private def setCtrlStack (s : MachineState) (scr' : SoATier) (stack' : KontStack)
    (nextCtrl : Control) : MachineState :=
  { s with scr := scr', ctrl := nextCtrl, stack := stack', stepsUsed := s.stepsUsed + 1, status := .running }

private def pushFrame (s : MachineState) (scr' : SoATier) (f : Frame)
    (nextCtrl : Control) : MachineState :=
  if s.stack.length < s.cfg.maxFrames then
    { s with
      scr := scr'
      ctrl := nextCtrl
      stack := f :: s.stack
      stepsUsed := s.stepsUsed + 1
      status := .running }
  else
    { s with
      scr := scr'
      status := .delegate .stackExhausted
      stepsUsed := s.stepsUsed + 1 }

private def failErr (s : MachineState) (code : ErrCode) : MachineState :=
  { s with status := .err code, stepsUsed := s.stepsUsed + 1 }

private def failDelegate (s : MachineState) (reason : DelegateReason) : MachineState :=
  { s with status := .delegate reason, stepsUsed := s.stepsUsed + 1 }

private def finishOk (s : MachineState) (ty : EIdx) : MachineState :=
  { s with status := .ok ty, stepsUsed := s.stepsUsed + 1 }

/-- One step from `.evalInfer ctx e`. -/
def stepEvalInfer (s : MachineState) (ctx : List EIdx) (e : EIdx) : MachineState :=
  match Arena.lookupNode s.pers s.scr e with
  | none => failErr s .danglingHandle
  | some (.bvar _) => failErr s .unboundBVar
  | some (.fvar id) =>
    match ctx[id.toNat]? with
    | none => failErr s .unboundFVar
    | some ty => goCtrl s s.scr (.retInfer ty)
  | some (.sort lvl) =>
    if lvl.toNat + 1 < 4294967296 then
      match allocScr s.cfg s.scr (.sort (UInt32.ofNat (lvl.toNat + 1))) with
      | .ok scr₁ res => goCtrl s scr₁ (.retInfer res)
      | .err c => failErr s c
      | .delegate r => failDelegate s r
    else
      failDelegate s .intOverflow
  | some (.const cid) =>
    match s.gpuEnv[cid.toNat]? with
    | none => failErr s .unknownConst
    | some decl => goCtrl s s.scr (.retInfer decl.ty)
  | some (.app fn arg) =>
    pushFrame s s.scr (.appFn ctx arg) (.evalInfer ctx fn)
  | some (.lam dom body) =>
    pushFrame s s.scr (.lamDom ctx dom body) (.evalInfer ctx dom)
  | some (.forallE dom body) =>
    pushFrame s s.scr (.forallDom ctx dom body) (.evalInfer ctx dom)
  | some (.letE ty val body) =>
    pushFrame s s.scr (.letTy ctx ty val body) (.evalInfer ctx ty)

/-- One step from `.evalWhnf e`. -/
def stepEvalWhnf (s : MachineState) (e : EIdx) : MachineState :=
  match Arena.lookupNode s.pers s.scr e with
  | none => failErr s .danglingHandle
  | some (.bvar _) | some (.fvar _) | some (.sort _)
  | some (.lam _ _) | some (.forallE _ _) =>
    goCtrl s s.scr (.retWhnf e)
  | some (.const cid) =>
    match s.gpuEnv[cid.toNat]? with
    | none => goCtrl s s.scr (.retWhnf e)
    | some decl =>
      match decl.val? with
      | none => goCtrl s s.scr (.retWhnf e)
      | some body => goCtrl s s.scr (.evalWhnf body)
  | some (.letE _ val body) =>
    match scratchInst s.cfg s.pers s.scr s.cfg.maxSteps 0 val body with
    | .ok scr₁ body' => goCtrl s scr₁ (.evalWhnf body')
    | .err c => failErr s c
    | .delegate r => failDelegate s r
  | some (.app fn arg) =>
    pushFrame s s.scr (.whnfApp arg) (.evalWhnf fn)

/-- One step from `.evalDefEq fid a b`. -/
def stepEvalDefEq (s : MachineState) (fid : Nat) (a b : EIdx) : MachineState :=
  if a.word == b.word then
    goCtrl s s.scr (.retDefEq true)
  else
    pushFrame s s.scr (.defEqLhs fid b) (.evalWhnf a)

/-- Helper dispatching two WHNF expression cells in `.defEqRhs`. -/
def stepDefEqRhsCells (s : MachineState) (fid : Nat) (rest : KontStack)
    (c₁ c₂ : ExprCell) : MachineState :=
  match c₁, c₂ with
  | .bvar i, .bvar j => setCtrlStack s s.scr rest (.retDefEq (i.toNat == j.toNat))
  | .fvar i, .fvar j => setCtrlStack s s.scr rest (.retDefEq (i.toNat == j.toNat))
  | .sort u, .sort v => setCtrlStack s s.scr rest (.retDefEq (u.toNat == v.toNat))
  | .const k₁, .const k₂ => setCtrlStack s s.scr rest (.retDefEq (k₁.toNat == k₂.toNat))
  | .app f₁ a₁, .app f₂ a₂ =>
    setCtrlStack s s.scr (.defEqSecond fid a₁ a₂ :: rest) (.evalDefEq fid f₁ f₂)
  | .lam d₁ b₁, .lam d₂ b₂ =>
    if fid < 4294967296 then
      match allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₁ fv =>
        match scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv b₁ with
        | .err c => failErr s c
        | .delegate r => failDelegate s r
        | .ok scr₂ b₁' =>
          match scratchInst s.cfg s.pers scr₂ s.cfg.maxSteps 0 fv b₂ with
          | .err c => failErr s c
          | .delegate r => failDelegate s r
          | .ok scr₃ b₂' =>
            setCtrlStack s scr₃ (.defEqSecond (fid + 1) b₁' b₂' :: rest) (.evalDefEq fid d₁ d₂)
    else
      failDelegate s .intOverflow
  | .forallE d₁ b₁, .forallE d₂ b₂ =>
    if fid < 4294967296 then
      match allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₁ fv =>
        match scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv b₁ with
        | .err c => failErr s c
        | .delegate r => failDelegate s r
        | .ok scr₂ b₁' =>
          match scratchInst s.cfg s.pers scr₂ s.cfg.maxSteps 0 fv b₂ with
          | .err c => failErr s c
          | .delegate r => failDelegate s r
          | .ok scr₃ b₂' =>
            setCtrlStack s scr₃ (.defEqSecond (fid + 1) b₁' b₂' :: rest) (.evalDefEq fid d₁ d₂)
    else
      failDelegate s .intOverflow
  | _, _ => setCtrlStack s s.scr rest (.retDefEq false)

/-- One step processing `.retInfer ty` against top frame `f`. -/
def stepRetInfer (s : MachineState) (f : Frame) (rest : KontStack) (ty : EIdx) : MachineState :=
  match f with
  | .appFn ctx arg =>
    setCtrlStack s s.scr (.appWhnf ctx arg :: rest) (.evalWhnf ty)
  | .appArg ctx dom cod arg =>
    setCtrlStack s s.scr (.appDefEq cod arg :: rest) (.evalDefEq ctx.length ty dom)
  | .lamDom ctx dom body =>
    setCtrlStack s s.scr (.lamDomWhnf ctx dom body :: rest) (.evalWhnf ty)
  | .lamBody fid dom =>
    match scratchAbst s.cfg s.pers s.scr s.cfg.maxSteps 0 fid ty with
    | .err c => failErr s c
    | .delegate r => failDelegate s r
    | .ok scr₁ tyAbs =>
      match allocScr s.cfg scr₁ (.forallE dom tyAbs) with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₂ res => setCtrlStack s scr₂ rest (.retInfer res)
  | .forallDom ctx dom body =>
    setCtrlStack s s.scr (.forallDomWhnf ctx dom body :: rest) (.evalWhnf ty)
  | .forallBody u =>
    setCtrlStack s s.scr (.forallBodyWhnf u :: rest) (.evalWhnf ty)
  | .letTy ctx t val body =>
    setCtrlStack s s.scr (.letTyWhnf ctx t val body :: rest) (.evalWhnf ty)
  | .letVal ctx t val body =>
    setCtrlStack s s.scr (.letValDefEq ctx t val body :: rest) (.evalDefEq ctx.length ty t)
  | .letBody fid t val =>
    match scratchAbst s.cfg s.pers s.scr s.cfg.maxSteps 0 fid ty with
    | .err c => failErr s c
    | .delegate r => failDelegate s r
    | .ok scr₁ tyAbs =>
      match allocScr s.cfg scr₁ (.letE t val tyAbs) with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₂ res => setCtrlStack s scr₂ rest (.retInfer res)
  | _ => failErr s .danglingHandle

/-- One step processing `.retWhnf w` against top frame `f`. -/
def stepRetWhnf (s : MachineState) (f : Frame) (rest : KontStack) (w : EIdx) : MachineState :=
  match f with
  | .appWhnf ctx arg =>
    match Arena.lookupNode s.pers s.scr w with
    | none => failErr s .danglingHandle
    | some (.forallE dom cod) =>
      setCtrlStack s s.scr (.appArg ctx dom cod arg :: rest) (.evalInfer ctx arg)
    | some _ => failErr s .expectedPi
  | .lamDomWhnf ctx dom body =>
    match Arena.lookupNode s.pers s.scr w with
    | none => failErr s .danglingHandle
    | some (.sort _) =>
      let fid := ctx.length
      if fid < 4294967296 then
        match allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
        | .err c => failErr s c
        | .delegate r => failDelegate s r
        | .ok scr₁ fv =>
          match scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv body with
          | .err c => failErr s c
          | .delegate r => failDelegate s r
          | .ok scr₂ body' =>
            setCtrlStack s scr₂ (.lamBody fid dom :: rest) (.evalInfer (ctx ++ [dom]) body')
      else
        failDelegate s .intOverflow
    | some _ => failErr s .expectedSort
  | .forallDomWhnf ctx dom body =>
    match Arena.lookupNode s.pers s.scr w with
    | none => failErr s .danglingHandle
    | some (.sort u) =>
      let fid := ctx.length
      if fid < 4294967296 then
        match allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
        | .err c => failErr s c
        | .delegate r => failDelegate s r
        | .ok scr₁ fv =>
          match scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv body with
          | .err c => failErr s c
          | .delegate r => failDelegate s r
          | .ok scr₂ body' =>
            setCtrlStack s scr₂ (.forallBody u :: rest) (.evalInfer (ctx ++ [dom]) body')
      else
        failDelegate s .intOverflow
    | some _ => failErr s .expectedSort
  | .forallBodyWhnf u =>
    match Arena.lookupNode s.pers s.scr w with
    | none => failErr s .danglingHandle
    | some (.sort v) =>
      match allocScr s.cfg s.scr (.sort (UInt32.ofNat (imax u.toNat v.toNat))) with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₁ res => setCtrlStack s scr₁ rest (.retInfer res)
    | some _ => failErr s .expectedSort
  | .letTyWhnf ctx ty val body =>
    match Arena.lookupNode s.pers s.scr w with
    | none => failErr s .danglingHandle
    | some (.sort _) =>
      setCtrlStack s s.scr (.letVal ctx ty val body :: rest) (.evalInfer ctx val)
    | some _ => failErr s .expectedSort
  | .whnfApp arg =>
    match Arena.lookupNode s.pers s.scr w with
    | none => failErr s .danglingHandle
    | some (.lam _ body) =>
      match scratchInst s.cfg s.pers s.scr s.cfg.maxSteps 0 arg body with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₁ body' => setCtrlStack s scr₁ rest (.evalWhnf body')
    | some _ =>
      match allocScr s.cfg s.scr (.app w arg) with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₁ res => setCtrlStack s scr₁ rest (.retWhnf res)
  | .defEqLhs fid b =>
    setCtrlStack s s.scr (.defEqRhs fid w :: rest) (.evalWhnf b)
  | .defEqRhs fid wa =>
    match Arena.lookupNode s.pers s.scr wa, Arena.lookupNode s.pers s.scr w with
    | none, _ | _, none => failErr s .danglingHandle
    | some c₁, some c₂ => stepDefEqRhsCells s fid rest c₁ c₂
  | _ => failErr s .danglingHandle

/-- One step processing `.retDefEq ok` against top frame `f`. -/
def stepRetDefEq (s : MachineState) (f : Frame) (rest : KontStack) (ok : Bool) : MachineState :=
  match f with
  | .appDefEq cod arg =>
    if ok then
      match scratchInst s.cfg s.pers s.scr s.cfg.maxSteps 0 arg cod with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₁ res => setCtrlStack s scr₁ rest (.retInfer res)
    else
      failErr s .appTypeMismatch
  | .letValDefEq ctx ty val body =>
    if ok then
      let fid := ctx.length
      if fid < 4294967296 then
        match allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
        | .err c => failErr s c
        | .delegate r => failDelegate s r
        | .ok scr₁ fv =>
          match scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv body with
          | .err c => failErr s c
          | .delegate r => failDelegate s r
          | .ok scr₂ body' =>
            setCtrlStack s scr₂ (.letBody fid ty val :: rest) (.evalInfer (ctx ++ [ty]) body')
      else
        failDelegate s .intOverflow
    else
      failErr s .letTypeMismatch
  | .defEqSecond fid₂ e₁ e₂ =>
    if ok then
      setCtrlStack s s.scr rest (.evalDefEq fid₂ e₁ e₂)
    else
      setCtrlStack s s.scr rest (.retDefEq false)
  | _ => failErr s .danglingHandle

/-- Full single-step transition of the bounded stackless GPU state machine. -/
def step (s : MachineState) : MachineState :=
  if s.status ≠ .running then
    s
  else if s.cfg.maxSteps ≤ s.stepsUsed then
    { s with status := .delegate .stepExhausted }
  else
    match s.ctrl with
    | .evalInfer ctx e => stepEvalInfer s ctx e
    | .evalWhnf e => stepEvalWhnf s e
    | .evalDefEq fid a b => stepEvalDefEq s fid a b
    | .retInfer ty =>
      match s.stack with
      | [] => finishOk s ty
      | f :: rest => stepRetInfer s f rest ty
    | .retWhnf w =>
      match s.stack with
      | [] => failErr s .danglingHandle
      | f :: rest => stepRetWhnf s f rest w
    | .retDefEq ok =>
      match s.stack with
      | [] => failErr s .danglingHandle
      | f :: rest => stepRetDefEq s f rest ok

/-- Iterate `step` up to `fuel` times. -/
def runMachine : Nat -> MachineState -> MachineState
  | 0, s => s
  | n + 1, s => runMachine n (step s)

/-- Final machine status after `n` steps. -/
def runSteps (n : Nat) (s : MachineState) : MachineStatus EIdx :=
  (runMachine n s).status

/-! ### 3. Delegation Safety (`delegate_never_accepts`) -/

theorem step_nonrunning {s : MachineState} (hnr : s.status ≠ .running) :
    step s = s := by
  unfold step
  simp [hnr]

theorem runMachine_nonrunning (n : Nat) {s : MachineState} (hnr : s.status ≠ .running) :
    runMachine n s = s := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [runMachine, step_nonrunning hnr]
    exact ih

theorem delegate_absorbing (n : Nat) {s : MachineState} {r : DelegateReason}
    (hd : s.status = .delegate r) :
    (runMachine n s).status = .delegate r := by
  have hnr : s.status ≠ .running := by rw [hd]; intro h; cases h
  rw [runMachine_nonrunning n hnr, hd]

theorem delegate_never_accepts (n : Nat) {s : MachineState} {r : DelegateReason} {ty : EIdx}
    (hd : s.status = .delegate r) :
    runSteps n s ≠ .ok ty := by
  unfold runSteps
  rw [delegate_absorbing n hd]
  intro h
  cases h

theorem stepExhausted_never_ok {s : MachineState} (hs : s.status = .running)
    (hmax : s.cfg.maxSteps ≤ s.stepsUsed) :
    ∀ {n : Nat} {ty : EIdx}, n ≥ 1 -> runSteps n s ≠ .ok ty
  | 0, _, h => by omega
  | k + 1, ty, _ => by
    have hstep : step s = { s with status := .delegate .stepExhausted } := by
      unfold step
      simp [hs, hmax]
    unfold runSteps runMachine
    rw [hstep]
    exact delegate_never_accepts k (by rfl)

/-- Multi-step compositionality for `runMachine`. -/
theorem runMachine_add (m n : Nat) (s : MachineState) :
    runMachine (m + n) s = runMachine n (runMachine m s) := by
  induction m generalizing s with
  | zero => simp [runMachine]
  | succ m ih =>
    rw [Nat.succ_add]
    exact ih (step s)

theorem runSteps_delegate_monotonic {s : MachineState} {k n : Nat} {r : DelegateReason}
    {ty : EIdx} (hle : k ≤ n) (hd : (runMachine k s).status = .delegate r) :
    runSteps n s = .delegate r ∧ runSteps n s ≠ .ok ty := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold runSteps
  rw [runMachine_add k d s]
  have hres := delegate_absorbing d hd
  refine ⟨hres, ?_⟩
  rw [hres]
  intro h
  cases h

/-! ### 4. Semantic Invariants (`InterpretsCtx`, `EnvSound`, `FrameOK`, `StateOK`) -/

def InterpretsCtx (pers scr : SoATier) (ctx : List EIdx) (kctx : List KExpr) : Prop :=
  ctx.length = kctx.length ∧
  ∀ (i : Nat) (e : EIdx), ctx[i]? = some e ->
    ∃ ke, kctx[i]? = some ke ∧ Interprets pers scr e ke

theorem interpretsCtx_nil (pers scr : SoATier) : InterpretsCtx pers scr [] [] := by
  refine ⟨rfl, ?_⟩
  intro i e h
  simp at h

theorem interpretsCtx_extends {pers scr scr' : SoATier} (hex : TierExtends scr scr')
    {ctx : List EIdx} {kctx : List KExpr} (hc : InterpretsCtx pers scr ctx kctx) :
    InterpretsCtx pers scr' ctx kctx := by
  refine ⟨hc.1, ?_⟩
  intro i e h
  obtain ⟨ke, hke, hi⟩ := hc.2 i e h
  exact ⟨ke, hke, interprets_extends hex hi⟩

private theorem list_getElem?_append {α : Type} (xs : List α) (x : α) (i : Nat) :
    (xs ++ [x])[i]? =
      if i < xs.length then xs[i]?
      else if i == xs.length then some x
      else none := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, List.getElem?_cons_succ, List.length_cons]
      rw [ih k]
      by_cases hk : k < as.length
      · have h1 : k + 1 < as.length + 1 := by omega
        simp [hk, h1]
      · by_cases heq : k = as.length
        · subst heq; simp
        · have h1 : ¬ (k + 1 < as.length + 1) := by omega
          have h2 : ¬ (k + 1 == as.length + 1) = true := by simp only [beq_iff_eq]; omega
          have h3 : ¬ (k == as.length) = true := by simp only [beq_iff_eq]; omega
          simp [hk, h1, h2, h3]

theorem interpretsCtx_snoc {pers scr : SoATier} {ctx : List EIdx} {kctx : List KExpr}
    {e : EIdx} {ke : KExpr} (hc : InterpretsCtx pers scr ctx kctx)
    (he : Interprets pers scr e ke) :
    InterpretsCtx pers scr (ctx ++ [e]) (kctx ++ [ke]) := by
  refine ⟨by simp [hc.1], ?_⟩
  intro i x h
  rw [list_getElem?_append] at h
  rw [list_getElem?_append, ← hc.1]
  by_cases hlt : i < ctx.length
  · simp only [hlt, ↓reduceIte] at h ⊢
    exact hc.2 i x h
  · by_cases heq : i = ctx.length
    · subst heq
      simp only [Nat.lt_irrefl, ↓reduceIte, beq_self_eq_true, Option.some.injEq] at h ⊢
      subst h
      exact ⟨ke, rfl, he⟩
    · have hbeq : ¬ ((i == ctx.length) = true) := by simp [beq_iff_eq, heq]
      simp only [hlt, ↓reduceIte, hbeq] at h
      cases h

private theorem envSound_none {pers : SoATier} {gpuEnv : Array GpuConstDecl} {env : KEnv}
    (hs : EnvSound pers gpuEnv env) {cid : Nat} (hn : gpuEnv[cid]? = none) :
    env[cid]? = none := by
  have h := hs cid
  rw [hn] at h
  cases hkd : env[cid]? with
  | none => rfl
  | some _ => simp [hkd] at h

private theorem envSound_some {pers : SoATier} {gpuEnv : Array GpuConstDecl} {env : KEnv}
    (hs : EnvSound pers gpuEnv env) {cid : Nat} {gd : GpuConstDecl}
    (hgd : gpuEnv[cid]? = some gd) :
    ∃ kd : ConstDecl, env[cid]? = some kd ∧
      Interprets pers .empty gd.ty kd.ty ∧
      (∀ v, gd.val? = some v -> ∃ kv, kd.val? = some kv ∧ Interprets pers .empty v kv) ∧
      (gd.val? = none -> kd.val? = none) := by
  have h := hs cid
  rw [hgd] at h
  cases hkd : env[cid]? with
  | none => simp [hkd] at h
  | some kd =>
    simp only [hkd] at h
    refine ⟨kd, rfl, h.1, ?_, ?_⟩
    · intro v hv
      have h2 := h.2
      rw [hv] at h2
      cases hkv : kd.val? with
      | none => simp [hkv] at h2
      | some kv => simp only [hkv] at h2; exact ⟨kv, rfl, h2⟩
    · intro hvn
      have h2 := h.2
      rw [hvn] at h2
      cases hkv : kd.val? with
      | none => rfl
      | some _ => simp [hkv] at h2

/-- Semantic sub-goal carried between caller and callee frames. -/
inductive SubGoal where
  | infer (kctx : List KExpr) (ke : KExpr)
  | whnf (ke : KExpr)
  | defEq (fid : Nat) (ka kb : KExpr)

/-- Edge correctness for one continuation frame transforming `inGoal` into `outGoal`. -/
def FrameOK (env : KEnv) (pers scr : SoATier) (f : Frame) (inGoal outGoal : SubGoal) : Prop :=
  match f with
  | .appFn ctx arg =>
    ∃ kctx kfn karg,
      inGoal = .infer kctx kfn ∧ outGoal = .infer kctx (.app kfn karg) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr arg karg
  | .appWhnf ctx arg =>
    ∃ kctx kfn karg kfty,
      inGoal = .whnf kfty ∧ outGoal = .infer kctx (.app kfn karg) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr arg karg ∧
      (∃ f₁, inferSpec env f₁ kctx kfn = some kfty)
  | .appArg ctx dom cod arg =>
    ∃ kctx kfn karg kdom kcod,
      inGoal = .infer kctx karg ∧ outGoal = .infer kctx (.app kfn karg) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr arg karg ∧
      Interprets pers scr dom kdom ∧ Interprets pers scr cod kcod ∧
      (∃ f₁ f₂ kfty, inferSpec env f₁ kctx kfn = some kfty ∧
        whnfFuel env f₂ kfty = some (.forallE kdom kcod))
  | .appDefEq cod arg =>
    ∃ kctx kfn karg kdom kcod katy,
      inGoal = .defEq kctx.length katy kdom ∧ outGoal = .infer kctx (.app kfn karg) ∧
      Interprets pers scr cod kcod ∧ Interprets pers scr arg karg ∧
      (∃ f₁ f₂ f₃ kfty, inferSpec env f₁ kctx kfn = some kfty ∧
        whnfFuel env f₂ kfty = some (.forallE kdom kcod) ∧
        inferSpec env f₃ kctx karg = some katy)
  | .lamDom ctx dom body =>
    ∃ kctx kdom kbody,
      inGoal = .infer kctx kdom ∧ outGoal = .infer kctx (.lam kdom kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr dom kdom ∧
      Interprets pers scr body kbody
  | .lamDomWhnf ctx dom body =>
    ∃ kctx kdom kbody kdomTy,
      inGoal = .whnf kdomTy ∧ outGoal = .infer kctx (.lam kdom kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr dom kdom ∧
      Interprets pers scr body kbody ∧ (∃ f₁, inferSpec env f₁ kctx kdom = some kdomTy)
  | .lamBody fid dom =>
    ∃ kctx kdom kbody kdomTy u,
      fid = kctx.length ∧
      inGoal = .infer (kctx ++ [kdom]) (kbody.inst 0 (.fvar fid)) ∧
      outGoal = .infer kctx (.lam kdom kbody) ∧
      Interprets pers scr dom kdom ∧
      (∃ f₁ f₂, inferSpec env f₁ kctx kdom = some kdomTy ∧
        whnfFuel env f₂ kdomTy = some (.sort u))
  | .forallDom ctx dom body =>
    ∃ kctx kdom kbody,
      inGoal = .infer kctx kdom ∧ outGoal = .infer kctx (.forallE kdom kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr dom kdom ∧
      Interprets pers scr body kbody
  | .forallDomWhnf ctx dom body =>
    ∃ kctx kdom kbody kdomTy,
      inGoal = .whnf kdomTy ∧ outGoal = .infer kctx (.forallE kdom kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr dom kdom ∧
      Interprets pers scr body kbody ∧ (∃ f₁, inferSpec env f₁ kctx kdom = some kdomTy)
  | .forallBody u =>
    ∃ kctx kdom kbody kdomTy,
      inGoal = .infer (kctx ++ [kdom]) (kbody.inst 0 (.fvar kctx.length)) ∧
      outGoal = .infer kctx (.forallE kdom kbody) ∧
      (∃ f₁ f₂, inferSpec env f₁ kctx kdom = some kdomTy ∧
        whnfFuel env f₂ kdomTy = some (.sort u.toNat))
  | .forallBodyWhnf u =>
    ∃ kctx kdom kbody kdomTy kbodyTy,
      inGoal = .whnf kbodyTy ∧ outGoal = .infer kctx (.forallE kdom kbody) ∧
      (∃ f₁ f₂ f₃, inferSpec env f₁ kctx kdom = some kdomTy ∧
        whnfFuel env f₂ kdomTy = some (.sort u.toNat) ∧
        inferSpec env f₃ (kctx ++ [kdom]) (kbody.inst 0 (.fvar kctx.length)) = some kbodyTy)
  | .letTy ctx ty val body =>
    ∃ kctx kty kval kbody,
      inGoal = .infer kctx kty ∧ outGoal = .infer kctx (.letE kty kval kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr ty kty ∧
      Interprets pers scr val kval ∧ Interprets pers scr body kbody
  | .letTyWhnf ctx ty val body =>
    ∃ kctx kty kval kbody ktyTy,
      inGoal = .whnf ktyTy ∧ outGoal = .infer kctx (.letE kty kval kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr ty kty ∧
      Interprets pers scr val kval ∧ Interprets pers scr body kbody ∧
      (∃ f₁, inferSpec env f₁ kctx kty = some ktyTy)
  | .letVal ctx ty val body =>
    ∃ kctx kty kval kbody ktyTy u,
      inGoal = .infer kctx kval ∧ outGoal = .infer kctx (.letE kty kval kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr ty kty ∧
      Interprets pers scr val kval ∧ Interprets pers scr body kbody ∧
      (∃ f₁ f₂, inferSpec env f₁ kctx kty = some ktyTy ∧
        whnfFuel env f₂ ktyTy = some (.sort u))
  | .letValDefEq ctx ty val body =>
    ∃ kctx kty kval kbody ktyTy kvalTy u,
      inGoal = .defEq kctx.length kvalTy kty ∧ outGoal = .infer kctx (.letE kty kval kbody) ∧
      InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr ty kty ∧
      Interprets pers scr val kval ∧ Interprets pers scr body kbody ∧
      (∃ f₁ f₂ f₃, inferSpec env f₁ kctx kty = some ktyTy ∧
        whnfFuel env f₂ ktyTy = some (.sort u) ∧ inferSpec env f₃ kctx kval = some kvalTy)
  | .letBody fid ty val =>
    ∃ kctx kty kval kbody ktyTy kvalTy u,
      fid = kctx.length ∧
      inGoal = .infer (kctx ++ [kty]) (kbody.inst 0 (.fvar fid)) ∧
      outGoal = .infer kctx (.letE kty kval kbody) ∧
      Interprets pers scr ty kty ∧ Interprets pers scr val kval ∧
      (∃ f₁ f₂ f₃ f₄, inferSpec env f₁ kctx kty = some ktyTy ∧
        whnfFuel env f₂ ktyTy = some (.sort u) ∧ inferSpec env f₃ kctx kval = some kvalTy ∧
        defEqSpec env f₄ fid kvalTy kty = true)
  | .whnfApp arg =>
    ∃ kfn karg origKe,
      inGoal = .whnf kfn ∧ outGoal = .whnf origKe ∧ Interprets pers scr arg karg ∧
      (∀ kw f, whnfFuel env f (.app kfn karg) = some kw -> ∃ f', whnfFuel env f' origKe = some kw)
  | .defEqLhs fid b =>
    ∃ ka kb origFid origKa origKb,
      inGoal = .whnf ka ∧ outGoal = .defEq origFid origKa origKb ∧
      Interprets pers scr b kb ∧
      ((∃ f, defEqSpec env f fid ka kb = true) -> ∃ f', defEqSpec env f' origFid origKa origKb = true)
  | .defEqRhs fid wa =>
    ∃ ka kb kwa origFid origKa origKb,
      inGoal = .whnf kb ∧ outGoal = .defEq origFid origKa origKb ∧
      Interprets pers scr wa kwa ∧ (∃ f₁, whnfFuel env f₁ ka = some kwa) ∧
      ((∃ f, defEqSpec env f fid ka kb = true) -> ∃ f', defEqSpec env f' origFid origKa origKb = true)
  | .defEqSecond fid₂ e₁ e₂ =>
    ∃ fid₁ x₁ x₂ origFid origKa origKb y₁ y₂,
      inGoal = .defEq fid₁ x₁ x₂ ∧ outGoal = .defEq origFid origKa origKb ∧
      Interprets pers scr e₁ y₁ ∧ Interprets pers scr e₂ y₂ ∧
      ((∃ f₃, defEqSpec env f₃ fid₁ x₁ x₂ = true) ->
        (∃ f₄, defEqSpec env f₄ fid₂ y₁ y₂ = true) ->
        ∃ f', defEqSpec env f' origFid origKa origKb = true)

theorem frameOK_extends {env : KEnv} {pers scr scr' : SoATier} (hex : TierExtends scr scr') :
    ∀ {f : Frame} {g₁ g₂ : SubGoal},
      FrameOK env pers scr f g₁ g₂ -> FrameOK env pers scr' f g₁ g₂ := by
  intro f g₁ g₂ hf
  cases f with
  | appFn ctx arg =>
    rcases hf with ⟨kctx, kfn, karg, hg1, hg2, hctx, harg⟩
    exact ⟨kctx, kfn, karg, hg1, hg2, interpretsCtx_extends hex hctx, interprets_extends hex harg⟩
  | appWhnf ctx arg =>
    rcases hf with ⟨kctx, kfn, karg, kfty, hg1, hg2, hctx, harg, hw⟩
    exact ⟨kctx, kfn, karg, kfty, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex harg, hw⟩
  | appArg ctx dom cod arg =>
    rcases hf with ⟨kctx, kfn, karg, kdom, kcod, hg1, hg2, hctx, harg, hdom, hcod, hw⟩
    exact ⟨kctx, kfn, karg, kdom, kcod, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex harg, interprets_extends hex hdom, interprets_extends hex hcod, hw⟩
  | appDefEq cod arg =>
    rcases hf with ⟨kctx, kfn, karg, kdom, kcod, katy, hg1, hg2, hcod, harg, hw⟩
    exact ⟨kctx, kfn, karg, kdom, kcod, katy, hg1, hg2,
           interprets_extends hex hcod, interprets_extends hex harg, hw⟩
  | lamDom ctx dom body =>
    rcases hf with ⟨kctx, kdom, kbody, hg1, hg2, hctx, hdom, hb⟩
    exact ⟨kctx, kdom, kbody, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hdom, interprets_extends hex hb⟩
  | lamDomWhnf ctx dom body =>
    rcases hf with ⟨kctx, kdom, kbody, kdomTy, hg1, hg2, hctx, hdom, hb, hw⟩
    exact ⟨kctx, kdom, kbody, kdomTy, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hdom, interprets_extends hex hb, hw⟩
  | lamBody fid dom =>
    rcases hf with ⟨kctx, kdom, kbody, kdomTy, u, hfid, hg1, hg2, hdom, hw⟩
    exact ⟨kctx, kdom, kbody, kdomTy, u, hfid, hg1, hg2, interprets_extends hex hdom, hw⟩
  | forallDom ctx dom body =>
    rcases hf with ⟨kctx, kdom, kbody, hg1, hg2, hctx, hdom, hb⟩
    exact ⟨kctx, kdom, kbody, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hdom, interprets_extends hex hb⟩
  | forallDomWhnf ctx dom body =>
    rcases hf with ⟨kctx, kdom, kbody, kdomTy, hg1, hg2, hctx, hdom, hb, hw⟩
    exact ⟨kctx, kdom, kbody, kdomTy, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hdom, interprets_extends hex hb, hw⟩
  | forallBody u => exact hf
  | forallBodyWhnf u => exact hf
  | letTy ctx ty val body =>
    rcases hf with ⟨kctx, kty, kval, kbody, hg1, hg2, hctx, hty, hval, hb⟩
    exact ⟨kctx, kty, kval, kbody, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hty, interprets_extends hex hval, interprets_extends hex hb⟩
  | letTyWhnf ctx ty val body =>
    rcases hf with ⟨kctx, kty, kval, kbody, ktyTy, hg1, hg2, hctx, hty, hval, hb, hw⟩
    exact ⟨kctx, kty, kval, kbody, ktyTy, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hty, interprets_extends hex hval, interprets_extends hex hb, hw⟩
  | letVal ctx ty val body =>
    rcases hf with ⟨kctx, kty, kval, kbody, ktyTy, u, hg1, hg2, hctx, hty, hval, hb, hw⟩
    exact ⟨kctx, kty, kval, kbody, ktyTy, u, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hty, interprets_extends hex hval, interprets_extends hex hb, hw⟩
  | letValDefEq ctx ty val body =>
    rcases hf with ⟨kctx, kty, kval, kbody, ktyTy, kvalTy, u, hg1, hg2, hctx, hty, hval, hb, hw⟩
    exact ⟨kctx, kty, kval, kbody, ktyTy, kvalTy, u, hg1, hg2, interpretsCtx_extends hex hctx,
           interprets_extends hex hty, interprets_extends hex hval, interprets_extends hex hb, hw⟩
  | letBody fid ty val =>
    rcases hf with ⟨kctx, kty, kval, kbody, ktyTy, kvalTy, u, hfid, hg1, hg2, hty, hval, hw⟩
    exact ⟨kctx, kty, kval, kbody, ktyTy, kvalTy, u, hfid, hg1, hg2,
           interprets_extends hex hty, interprets_extends hex hval, hw⟩
  | whnfApp arg =>
    rcases hf with ⟨kfn, karg, origKe, hg1, hg2, harg, htr⟩
    exact ⟨kfn, karg, origKe, hg1, hg2, interprets_extends hex harg, htr⟩
  | defEqLhs fid b =>
    rcases hf with ⟨ka, kb, origFid, origKa, origKb, hg1, hg2, hb, htr⟩
    exact ⟨ka, kb, origFid, origKa, origKb, hg1, hg2, interprets_extends hex hb, htr⟩
  | defEqRhs fid wa =>
    rcases hf with ⟨ka, kb, kwa, origFid, origKa, origKb, hg1, hg2, hwa, hw, htr⟩
    exact ⟨ka, kb, kwa, origFid, origKa, origKb, hg1, hg2, interprets_extends hex hwa, hw, htr⟩
  | defEqSecond fid₂ e₁ e₂ =>
    rcases hf with ⟨fid₁, x₁, x₂, origFid, origKa, origKb, y₁, y₂, hg1, hg2, he1, he2, htr⟩
    exact ⟨fid₁, x₁, x₂, origFid, origKa, origKb, y₁, y₂, hg1, hg2,
           interprets_extends hex he1, interprets_extends hex he2, htr⟩

def StackOK (env : KEnv) (pers scr : SoATier) (rootGoal : SubGoal) :
    SubGoal -> KontStack -> Prop
  | curGoal, [] => curGoal = rootGoal
  | curGoal, f :: rest =>
    ∃ nextGoal, FrameOK env pers scr f curGoal nextGoal ∧
      StackOK env pers scr rootGoal nextGoal rest

theorem stackOK_extends {env : KEnv} {pers scr scr' : SoATier} (hex : TierExtends scr scr')
    {rootGoal : SubGoal} :
    ∀ {stack : KontStack} {curGoal : SubGoal},
      StackOK env pers scr rootGoal curGoal stack ->
      StackOK env pers scr' rootGoal curGoal stack
  | [], _, h => h
  | _ :: _, _, ⟨nextGoal, hf, hrest⟩ =>
    ⟨nextGoal, frameOK_extends hex hf, stackOK_extends hex hrest⟩

def CtrlOK (env : KEnv) (pers scr : SoATier) (rootGoal : SubGoal)
    (ctrl : Control) (stack : KontStack) : Prop :=
  match ctrl with
  | .evalInfer ctx e =>
    ∃ kctx ke, InterpretsCtx pers scr ctx kctx ∧ Interprets pers scr e ke ∧
      StackOK env pers scr rootGoal (.infer kctx ke) stack
  | .evalWhnf e =>
    ∃ curKe origKe, Interprets pers scr e curKe ∧
      (∀ kw f, whnfFuel env f curKe = some kw -> ∃ f', whnfFuel env f' origKe = some kw) ∧
      StackOK env pers scr rootGoal (.whnf origKe) stack
  | .evalDefEq fid a b =>
    ∃ ka kb origFid origKa origKb,
      Interprets pers scr a ka ∧ Interprets pers scr b kb ∧
      ((∃ f, defEqSpec env f fid ka kb = true) ->
        ∃ f', defEqSpec env f' origFid origKa origKb = true) ∧
      StackOK env pers scr rootGoal (.defEq origFid origKa origKb) stack
  | .retInfer ty =>
    ∃ kctx ke kty, Interprets pers scr ty kty ∧
      (∃ fuel, inferSpec env fuel kctx ke = some kty) ∧
      StackOK env pers scr rootGoal (.infer kctx ke) stack
  | .retWhnf w =>
    ∃ origKe kw, Interprets pers scr w kw ∧
      (∃ fuel, whnfFuel env fuel origKe = some kw) ∧
      StackOK env pers scr rootGoal (.whnf origKe) stack
  | .retDefEq ok =>
    ∃ origFid origKa origKb,
      (ok = true -> ∃ f', defEqSpec env f' origFid origKa origKb = true) ∧
      StackOK env pers scr rootGoal (.defEq origFid origKa origKb) stack

def StateOK (env : KEnv) (pers : SoATier) (rootKE : KExpr) (s : MachineState) : Prop :=
  s.pers = pers ∧
  ScratchColsWF s.scr ∧
  (s.status = .running -> CtrlOK env pers s.scr (.infer [] rootKE) s.ctrl s.stack) ∧
  (∀ ty, s.status = .ok ty ->
    ∃ kty, Interprets pers s.scr ty kty ∧ ∃ fuel, inferSpec env fuel [] rootKE = some kty)

/-! ### 5. Single-Step Preservation Lemmas -/

private theorem stateOK_failErr {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} (hp : s.pers = pers) (wf : ScratchColsWF s.scr) (c : ErrCode) :
    StateOK env pers rootKE (failErr s c) := by
  unfold failErr
  exact ⟨hp, wf, (fun h => by cases h), (fun _ h => by cases h)⟩

private theorem stateOK_failDelegate {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} (hp : s.pers = pers) (wf : ScratchColsWF s.scr) (r : DelegateReason) :
    StateOK env pers rootKE (failDelegate s r) := by
  unfold failDelegate
  exact ⟨hp, wf, (fun h => by cases h), (fun _ h => by cases h)⟩

private theorem stateOK_pushFrame {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} (hp : s.pers = pers) {scr' : SoATier} (wf' : ScratchColsWF scr')
    {f : Frame} {nextCtrl : Control}
    (hc : CtrlOK env pers scr' (.infer [] rootKE) nextCtrl (f :: s.stack)) :
    StateOK env pers rootKE (pushFrame s scr' f nextCtrl) := by
  unfold pushFrame
  split
  · exact ⟨hp, wf', (fun _ => hc), (fun _ h => by cases h)⟩
  · exact ⟨hp, wf', (fun h => by cases h), (fun _ h => by cases h)⟩

private theorem stateOK_goCtrl {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} {scr' : SoATier} (hp : s.pers = pers) (wf' : ScratchColsWF scr')
    {ctrl' : Control}
    (hc : CtrlOK env pers scr' (.infer [] rootKE) ctrl' s.stack) :
    StateOK env pers rootKE (goCtrl s scr' ctrl') := by
  unfold goCtrl
  exact ⟨hp, wf', (fun _ => hc), (fun _ h => by cases h)⟩

private theorem stateOK_setCtrlStack {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} {scr' : SoATier} (hp : s.pers = pers) (wf' : ScratchColsWF scr')
    {stack' : KontStack} {ctrl' : Control}
    (hc : CtrlOK env pers scr' (.infer [] rootKE) ctrl' stack') :
    StateOK env pers rootKE (setCtrlStack s scr' stack' ctrl') := by
  unfold setCtrlStack
  exact ⟨hp, wf', (fun _ => hc), (fun _ h => by cases h)⟩

private theorem defEqSpec_of_whnf_leaf {env : KEnv} {f₁ f₂ fid : Nat}
    {ka kb kwa kwb : KExpr}
    (hwa : whnfFuel env f₁ ka = some kwa) (hwb : whnfFuel env f₂ kb = some kwb)
    (hmatch :
      match kwa, kwb with
      | .bvar i, .bvar j => (i == j) = true
      | .fvar i, .fvar j => (i == j) = true
      | .sort u, .sort v => (u == v) = true
      | .const c₁, .const c₂ => (c₁ == c₂) = true
      | _, _ => False) :
    ∃ f, defEqSpec env f fid ka kb = true := by
  have hwa' := whnfFuel_mono env (Nat.le_max_left f₁ f₂) ka kwa hwa
  have hwb' := whnfFuel_mono env (Nat.le_max_right f₁ f₂) kb kwb hwb
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp only [defEqSpec]
  by_cases heq : (ka == kb) = true
  · simp [heq]
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    rw [hwa', hwb']
    dsimp only
    cases kwa <;> cases kwb <;> dsimp only at hmatch ⊢
    all_goals first | exact hmatch | exact False.elim hmatch

private theorem defEqSpec_of_whnf_pair {env : KEnv} {f₁ f₂ fid fid₂ : Nat}
    {ka kb kwa kwb x₁ x₂ y₁ y₂ : KExpr}
    (hwa : whnfFuel env f₁ ka = some kwa) (hwb : whnfFuel env f₂ kb = some kwb)
    (hkind :
      (∃ f₁' a₁' f₂' a₂', kwa = .app f₁' a₁' ∧ kwb = .app f₂' a₂' ∧
        fid₂ = fid ∧ x₁ = f₁' ∧ x₂ = f₂' ∧ y₁ = a₁' ∧ y₂ = a₂') ∨
      (∃ d₁ b₁ d₂ b₂, kwa = .lam d₁ b₁ ∧ kwb = .lam d₂ b₂ ∧
        fid₂ = fid + 1 ∧ x₁ = d₁ ∧ x₂ = d₂ ∧
        y₁ = b₁.inst 0 (.fvar fid) ∧ y₂ = b₂.inst 0 (.fvar fid)) ∨
      (∃ d₁ b₁ d₂ b₂, kwa = .forallE d₁ b₁ ∧ kwb = .forallE d₂ b₂ ∧
        fid₂ = fid + 1 ∧ x₁ = d₁ ∧ x₂ = d₂ ∧
        y₁ = b₁.inst 0 (.fvar fid) ∧ y₂ = b₂.inst 0 (.fvar fid)))
    {fa fb : Nat}
    (hfa : defEqSpec env fa fid x₁ x₂ = true)
    (hfb : defEqSpec env fb fid₂ y₁ y₂ = true) :
    ∃ f, defEqSpec env f fid ka kb = true := by
  have hwa' := whnfFuel_mono env (Nat.le_trans (Nat.le_max_left f₁ f₂) (Nat.le_max_left (max f₁ f₂) (max fa fb))) ka kwa hwa
  have hwb' := whnfFuel_mono env (Nat.le_trans (Nat.le_max_right f₁ f₂) (Nat.le_max_left (max f₁ f₂) (max fa fb))) kb kwb hwb
  have ha' := defEqSpec_mono env (Nat.le_trans (Nat.le_max_left fa fb) (Nat.le_max_right (max f₁ f₂) _)) fid x₁ x₂ hfa
  have hb' := defEqSpec_mono env (Nat.le_trans (Nat.le_max_right fa fb) (Nat.le_max_right (max f₁ f₂) _)) fid₂ y₁ y₂ hfb
  refine ⟨max (max f₁ f₂) (max fa fb) + 1, ?_⟩
  simp only [defEqSpec]
  by_cases heq : (ka == kb) = true
  · simp [heq]
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    rw [hwa', hwb']
    dsimp only
    rcases hkind with
      ⟨f₁', a₁', f₂', a₂', rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨d₁, b₁, d₂, b₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨d₁, b₁, d₂, b₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [ha', hb', Bool.and_self]
    · simp only [ha', hb', Bool.and_self]
    · simp only [ha', hb', Bool.and_self]

theorem stepEvalInfer_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} {s : MachineState}
    (hp : s.pers = pers) (wf : ScratchColsWF s.scr) (henv : EnvSound pers s.gpuEnv env)
    {ctx : List EIdx} {e : EIdx}
    (hc : CtrlOK env pers s.scr (.infer [] rootKE) (.evalInfer ctx e) s.stack) :
    StateOK env pers rootKE (stepEvalInfer s ctx e) := by
  rcases hc with ⟨kctx, ke, hctx, he, hstk⟩
  unfold stepEvalInfer
  rw [hp]
  cases hl : Arena.lookupNode pers s.scr e with
  | none =>
    dsimp only
    exact stateOK_failErr hp wf .danglingHandle
  | some cell =>
    have hinv := interprets_invert pers s.scr he hl
    cases cell with
    | bvar idx => dsimp only; exact stateOK_failErr hp wf .unboundBVar
    | fvar id =>
      dsimp only
      dsimp only at hinv; subst hinv
      cases hget : ctx[id.toNat]? with
      | none => dsimp only; exact stateOK_failErr hp wf .unboundFVar
      | some ty =>
        dsimp only
        obtain ⟨kty, hkty, hity⟩ := hctx.2 id.toNat ty hget
        exact stateOK_goCtrl hp wf ⟨kctx, .fvar id.toNat, kty, hity, ⟨1, hkty⟩, hstk⟩
    | sort lvl =>
      dsimp only
      dsimp only at hinv; subst hinv
      split
      · next hlt =>
        cases ha : allocScr s.cfg s.scr (.sort (UInt32.ofNat (lvl.toNat + 1))) with
        | err c => exact stateOK_failErr hp wf c
        | delegate r => exact stateOK_failDelegate hp wf r
        | ok scr₁ res =>
          dsimp only
          have hwf := allocScr_wf pers wf ha
          have hex := allocScr_extends ha
          have hlook : Interprets pers scr₁ res (.sort (UInt32.ofNat (lvl.toNat + 1)).toNat) := by
            have h := interprets_of_lookup pers scr₁ hwf.2
            dsimp only at h
            exact h
          have hnat : (UInt32.ofNat (lvl.toNat + 1)).toNat = lvl.toNat + 1 := by
            change (lvl.toNat + 1) % 4294967296 = lvl.toNat + 1; omega
          rw [hnat] at hlook
          exact stateOK_goCtrl hp hwf.1
            ⟨kctx, .sort lvl.toNat, .sort (lvl.toNat + 1), hlook, ⟨1, rfl⟩,
              stackOK_extends hex hstk⟩
      · exact stateOK_failDelegate hp wf .intOverflow
    | const cid =>
      dsimp only
      dsimp only at hinv; subst hinv
      cases hgd : s.gpuEnv[cid.toNat]? with
      | none => dsimp only; exact stateOK_failErr hp wf .unknownConst
      | some gd =>
        dsimp only
        obtain ⟨kd, hkd, hty, _, _⟩ := envSound_some henv hgd
        have hty' : Interprets pers s.scr gd.ty kd.ty :=
          interprets_extends (tierExtends_empty s.scr) hty
        have hinf : inferSpec env 1 kctx (.const cid.toNat) = some kd.ty := by
          simp [inferSpec, hkd]
        exact stateOK_goCtrl hp wf ⟨kctx, .const cid.toNat, kd.ty, hty', ⟨1, hinf⟩, hstk⟩
    | app fn arg =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kfn, karg, rfl, hfn, harg⟩
      exact stateOK_pushFrame hp wf
        ⟨kctx, kfn, hctx, hfn,
          ⟨.infer kctx (.app kfn karg), ⟨kctx, kfn, karg, rfl, rfl, hctx, harg⟩, hstk⟩⟩
    | lam dom body =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kdom, kb, rfl, hdom, hb⟩
      exact stateOK_pushFrame hp wf
        ⟨kctx, kdom, hctx, hdom,
          ⟨.infer kctx (.lam kdom kb), ⟨kctx, kdom, kb, rfl, rfl, hctx, hdom, hb⟩, hstk⟩⟩
    | forallE dom body =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kdom, kb, rfl, hdom, hb⟩
      exact stateOK_pushFrame hp wf
        ⟨kctx, kdom, hctx, hdom,
          ⟨.infer kctx (.forallE kdom kb), ⟨kctx, kdom, kb, rfl, rfl, hctx, hdom, hb⟩, hstk⟩⟩
    | letE ty val body =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kty, kv, kb, rfl, hty, hv, hb⟩
      exact stateOK_pushFrame hp wf
        ⟨kctx, kty, hctx, hty,
          ⟨.infer kctx (.letE kty kv kb),
            ⟨kctx, kty, kv, kb, rfl, rfl, hctx, hty, hv, hb⟩, hstk⟩⟩

theorem stepEvalWhnf_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} {s : MachineState}
    (hp : s.pers = pers) (wf : ScratchColsWF s.scr) (henv : EnvSound pers s.gpuEnv env)
    {e : EIdx}
    (hc : CtrlOK env pers s.scr (.infer [] rootKE) (.evalWhnf e) s.stack) :
    StateOK env pers rootKE (stepEvalWhnf s e) := by
  rcases hc with ⟨curKe, origKe, he, htr, hstk⟩
  unfold stepEvalWhnf
  rw [hp]
  cases hl : Arena.lookupNode pers s.scr e with
  | none =>
    dsimp only
    exact stateOK_failErr hp wf .danglingHandle
  | some cell =>
    have hinv := interprets_invert pers s.scr he hl
    cases cell with
    | bvar idx =>
      dsimp only
      dsimp only at hinv; subst hinv
      obtain ⟨f', hf'⟩ := htr (.bvar idx.toNat) 1 rfl
      exact stateOK_goCtrl hp wf ⟨origKe, .bvar idx.toNat, he, ⟨f', hf'⟩, hstk⟩
    | fvar id =>
      dsimp only
      dsimp only at hinv; subst hinv
      obtain ⟨f', hf'⟩ := htr (.fvar id.toNat) 1 rfl
      exact stateOK_goCtrl hp wf ⟨origKe, .fvar id.toNat, he, ⟨f', hf'⟩, hstk⟩
    | sort lvl =>
      dsimp only
      dsimp only at hinv; subst hinv
      obtain ⟨f', hf'⟩ := htr (.sort lvl.toNat) 1 rfl
      exact stateOK_goCtrl hp wf ⟨origKe, .sort lvl.toNat, he, ⟨f', hf'⟩, hstk⟩
    | lam ty b =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kty, kb, rfl, _, _⟩
      obtain ⟨f', hf'⟩ := htr (.lam kty kb) 1 rfl
      exact stateOK_goCtrl hp wf ⟨origKe, .lam kty kb, he, ⟨f', hf'⟩, hstk⟩
    | forallE ty b =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kty, kb, rfl, _, _⟩
      obtain ⟨f', hf'⟩ := htr (.forallE kty kb) 1 rfl
      exact stateOK_goCtrl hp wf ⟨origKe, .forallE kty kb, he, ⟨f', hf'⟩, hstk⟩
    | const cid =>
      dsimp only
      dsimp only at hinv; subst hinv
      cases hgd : s.gpuEnv[cid.toNat]? with
      | none =>
        dsimp only
        have hnone := envSound_none henv hgd
        have hw1 : whnfFuel env 1 (.const cid.toNat) = some (.const cid.toNat) := by
          simp [whnfFuel, hnone]
        obtain ⟨f', hf'⟩ := htr (.const cid.toNat) 1 hw1
        exact stateOK_goCtrl hp wf ⟨origKe, .const cid.toNat, he, ⟨f', hf'⟩, hstk⟩
      | some gd =>
        dsimp only
        obtain ⟨kd, hkd, _, hval, hnoval⟩ := envSound_some henv hgd
        cases hv : gd.val? with
        | none =>
          dsimp only
          have hkv := hnoval hv
          have hw1 : whnfFuel env 1 (.const cid.toNat) = some (.const cid.toNat) := by
            simp [whnfFuel, hkd, hkv]
          obtain ⟨f', hf'⟩ := htr (.const cid.toNat) 1 hw1
          exact stateOK_goCtrl hp wf ⟨origKe, .const cid.toNat, he, ⟨f', hf'⟩, hstk⟩
        | some body =>
          dsimp only
          obtain ⟨kbody, hkval, hibody⟩ := hval body hv
          have hibody' := interprets_extends (tierExtends_empty s.scr) hibody
          refine stateOK_goCtrl hp wf ⟨kbody, origKe, hibody', ?_, hstk⟩
          intro kw f hwf
          apply htr kw (f + 1)
          simp only [whnfFuel, hkd, hkval]
          exact hwf
    | letE ty val body =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kty, kval, kbody, rfl, _, hval, hbody⟩
      cases hi : scratchInst s.cfg pers s.scr s.cfg.maxSteps 0 val body with
      | err c => exact stateOK_failErr hp wf c
      | delegate r => exact stateOK_failDelegate hp wf r
      | ok scr₁ body' =>
        dsimp only
        have ⟨wf₁, ex₁⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 val body body' wf hi
        have hsound := scratchInst_sound s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 val body body' kbody kval wf hbody hval hi
        refine stateOK_goCtrl hp wf₁ ⟨kbody.inst 0 kval, origKe, hsound, ?_, stackOK_extends ex₁ hstk⟩
        intro kw f hwf
        apply htr kw (f + 1)
        simp only [whnfFuel]
        exact hwf
    | app fn arg =>
      dsimp only
      dsimp only at hinv
      rcases hinv with ⟨kfn, karg, rfl, hfn, harg⟩
      exact stateOK_pushFrame hp wf
        ⟨kfn, kfn, hfn, fun _ f h => ⟨f, h⟩,
          ⟨.whnf origKe, ⟨kfn, karg, origKe, rfl, rfl, harg, htr⟩, hstk⟩⟩

theorem stepEvalDefEq_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} {s : MachineState}
    (hp : s.pers = pers) (wf : ScratchColsWF s.scr)
    {fid : Nat} {a b : EIdx}
    (hc : CtrlOK env pers s.scr (.infer [] rootKE) (.evalDefEq fid a b) s.stack) :
    StateOK env pers rootKE (stepEvalDefEq s fid a b) := by
  rcases hc with ⟨ka, kb, origFid, origKa, origKb, ha, hb, htr, hstk⟩
  unfold stepEvalDefEq
  split
  · next heq =>
    have haw : a = b := by
      rcases a with ⟨wa⟩; rcases b with ⟨wb⟩
      have hww : wa = wb := beq_iff_eq.mp heq
      subst hww; rfl
    subst haw
    have hkeq : ka = kb := interprets_deterministic ha hb
    subst hkeq
    have hspec : defEqSpec env 1 fid ka ka = true := by simp [defEqSpec]
    exact stateOK_goCtrl hp wf ⟨origFid, origKa, origKb, fun _ => htr ⟨1, hspec⟩, hstk⟩
  · exact stateOK_pushFrame hp wf
      ⟨ka, ka, ha, fun _ f h => ⟨f, h⟩,
        ⟨.defEq origFid origKa origKb,
          ⟨ka, kb, origFid, origKa, origKb, rfl, rfl, hb, htr⟩, hstk⟩⟩

theorem stepRetInfer_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} {s : MachineState}
    (hp : s.pers = pers) (wf : ScratchColsWF s.scr)
    {f : Frame} {rest : KontStack} {ty : EIdx}
    (hc : CtrlOK env pers s.scr (.infer [] rootKE) (.retInfer ty) (f :: rest)) :
    StateOK env pers rootKE (stepRetInfer s f rest ty) := by
  rcases hc with ⟨kctx, ke, kty, hty, ⟨f₀, hf₀⟩, ⟨nextGoal, hfr, hrest⟩⟩
  unfold stepRetInfer
  cases f with
  | appFn ctx arg =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kfn, karg, hg1, rfl, hctx, harg⟩
    cases hg1
    exact stateOK_setCtrlStack hp wf
      ⟨kty, kty, hty, fun _ f h => ⟨f, h⟩,
        ⟨.infer kctx (.app ke karg), ⟨kctx, ke, karg, kty, rfl, rfl, hctx, harg, ⟨f₀, hf₀⟩⟩, hrest⟩⟩
  | appArg ctx dom cod arg =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kfn, karg, kdom, kcod, hg1, rfl, hctx, harg, hdom, hcod, f₁, f₂, kfty, hf1, hf2⟩
    cases hg1
    have hlen : ctx.length = kctx.length := hctx.1
    rw [hlen]
    exact stateOK_setCtrlStack hp wf
      ⟨kty, kdom, kctx.length, kty, kdom, hty, hdom, fun h => h,
        ⟨.infer kctx (.app kfn ke),
          ⟨kctx, kfn, ke, kdom, kcod, kty, rfl, rfl, hcod, harg, ⟨f₁, f₂, f₀, kfty, hf1, hf2, hf₀⟩⟩, hrest⟩⟩
  | lamDom ctx dom body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kdom, kbody, hg1, rfl, hctx, hdom, hb⟩
    cases hg1
    exact stateOK_setCtrlStack hp wf
      ⟨kty, kty, hty, fun _ f h => ⟨f, h⟩,
        ⟨.infer kctx (.lam ke kbody), ⟨kctx, ke, kbody, kty, rfl, rfl, hctx, hdom, hb, ⟨f₀, hf₀⟩⟩, hrest⟩⟩
  | lamBody fid dom =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kdom, kbody, kdomTy, u, hfid, hg1, rfl, hdom, f₁, f₂, hf1, hf2⟩
    cases hg1
    rw [hp]
    cases ha : scratchAbst s.cfg pers s.scr s.cfg.maxSteps 0 fid ty with
    | err c => exact stateOK_failErr hp wf c
    | delegate r => exact stateOK_failDelegate hp wf r
    | ok scr₁ tyAbs =>
      dsimp only
      have ⟨wf₁, ex₁⟩ := scratchAbst_extends s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 fid ty tyAbs wf ha
      have htyAbs := scratchAbst_sound s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 fid ty tyAbs kty wf hty ha
      cases hmk : allocScr s.cfg scr₁ (.forallE dom tyAbs) with
      | err c => exact stateOK_failErr hp wf c
      | delegate r => exact stateOK_failDelegate hp wf r
      | ok scr₂ res =>
        dsimp only
        have ⟨wf₂, hl⟩ := allocScr_wf pers wf₁ hmk
        have ex₂ := allocScr_extends hmk
        have hres : Interprets pers scr₂ res (.forallE kdom (kty.abst 0 fid)) :=
          interprets_of_lookup pers scr₂ hl (interprets_extends (tierExtends_trans ex₁ ex₂) hdom)
            (interprets_extends ex₂ htyAbs)
        have hf1' := inferSpec_mono env (Nat.le_max_left f₁ (max f₂ f₀)) _ _ _ hf1
        have hf2' := whnfFuel_mono env (Nat.le_trans (Nat.le_max_left f₂ f₀) (Nat.le_max_right f₁ _)) _ _ hf2
        have hf0' := inferSpec_mono env (Nat.le_trans (Nat.le_max_right f₂ f₀) (Nat.le_max_right f₁ _)) _ _ _ hf₀
        subst hfid
        have hinf : inferSpec env (max f₁ (max f₂ f₀) + 1) kctx' (.lam kdom kbody) =
            some (.forallE kdom (kty.abst 0 kctx'.length)) := by
          simp only [inferSpec, hf1', hf2', hf0']
        exact stateOK_setCtrlStack hp wf₂
          ⟨kctx', .lam kdom kbody, .forallE kdom (kty.abst 0 kctx'.length), hres, ⟨max f₁ (max f₂ f₀) + 1, hinf⟩,
            stackOK_extends (tierExtends_trans ex₁ ex₂) hrest⟩
  | forallDom ctx dom body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kdom, kbody, hg1, rfl, hctx, hdom, hb⟩
    cases hg1
    exact stateOK_setCtrlStack hp wf
      ⟨kty, kty, hty, fun _ f h => ⟨f, h⟩,
        ⟨.infer kctx (.forallE ke kbody),
          ⟨kctx, ke, kbody, kty, rfl, rfl, hctx, hdom, hb, ⟨f₀, hf₀⟩⟩, hrest⟩⟩
  | forallBody u =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kdom, kbody, kdomTy, hg1, rfl, f₁, f₂, hf1, hf2⟩
    cases hg1
    exact stateOK_setCtrlStack hp wf
      ⟨kty, kty, hty, fun _ f h => ⟨f, h⟩,
        ⟨.infer kctx' (.forallE kdom kbody),
          ⟨kctx', kdom, kbody, kdomTy, kty, rfl, rfl, f₁, f₂, f₀, hf1, hf2, hf₀⟩, hrest⟩⟩
  | letTy ctx t val body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kt, kval, kbody, hg1, rfl, hctx, ht, hval, hb⟩
    cases hg1
    exact stateOK_setCtrlStack hp wf
      ⟨kty, kty, hty, fun _ f h => ⟨f, h⟩,
        ⟨.infer kctx (.letE ke kval kbody),
          ⟨kctx, ke, kval, kbody, kty, rfl, rfl, hctx, ht, hval, hb, ⟨f₀, hf₀⟩⟩, hrest⟩⟩
  | letVal ctx t val body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kt, kval, kbody, ktyTy, u, hg1, rfl, hctx, ht, hval, hb, f₁, f₂, hf1, hf2⟩
    cases hg1
    rw [hctx.1]
    exact stateOK_setCtrlStack hp wf
      ⟨kty, kt, kctx.length, kty, kt, hty, ht, fun h => h,
        ⟨.infer kctx (.letE kt ke kbody),
          ⟨kctx, kt, ke, kbody, ktyTy, kty, u, rfl, rfl, hctx, ht, hval, hb, ⟨f₁, f₂, f₀, hf1, hf2, hf₀⟩⟩, hrest⟩⟩
  | letBody fid t val =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx', kt, kval, kbody, ktyTy, kvalTy, u, hfid, hg1, rfl, ht, hval, f₁, f₂, f₃, f₄, hf1, hf2, hf3, hf4⟩
    cases hg1
    rw [hp]
    cases ha : scratchAbst s.cfg pers s.scr s.cfg.maxSteps 0 fid ty with
    | err c => exact stateOK_failErr hp wf c
    | delegate r => exact stateOK_failDelegate hp wf r
    | ok scr₁ tyAbs =>
      dsimp only
      have ⟨wf₁, ex₁⟩ := scratchAbst_extends s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 fid ty tyAbs wf ha
      have htyAbs := scratchAbst_sound s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 fid ty tyAbs kty wf hty ha
      cases hmk : allocScr s.cfg scr₁ (.letE t val tyAbs) with
      | err c => exact stateOK_failErr hp wf c
      | delegate r => exact stateOK_failDelegate hp wf r
      | ok scr₂ res =>
        dsimp only
        have ⟨wf₂, hl⟩ := allocScr_wf pers wf₁ hmk
        have ex₂ := allocScr_extends hmk
        have hres : Interprets pers scr₂ res (.letE kt kval (kty.abst 0 fid)) :=
          interprets_of_lookup pers scr₂ hl
            (interprets_extends (tierExtends_trans ex₁ ex₂) ht)
            (interprets_extends (tierExtends_trans ex₁ ex₂) hval)
            (interprets_extends ex₂ htyAbs)
        have hf1' := inferSpec_mono env (by omega : f₁ ≤ max f₁ (max f₂ (max f₃ (max f₄ f₀)))) _ _ _ hf1
        have hf2' := whnfFuel_mono env (by omega : f₂ ≤ max f₁ (max f₂ (max f₃ (max f₄ f₀)))) _ _ hf2
        have hf3' := inferSpec_mono env (by omega : f₃ ≤ max f₁ (max f₂ (max f₃ (max f₄ f₀)))) _ _ _ hf3
        have hf4' := defEqSpec_mono env (by omega : f₄ ≤ max f₁ (max f₂ (max f₃ (max f₄ f₀)))) _ _ _ hf4
        have hf0' := inferSpec_mono env (by omega : f₀ ≤ max f₁ (max f₂ (max f₃ (max f₄ f₀)))) _ _ _ hf₀
        subst hfid
        have hinf : inferSpec env (max f₁ (max f₂ (max f₃ (max f₄ f₀))) + 1) kctx' (.letE kt kval kbody) =
            some (.letE kt kval (kty.abst 0 kctx'.length)) := by
          simp only [inferSpec, hf1', hf3', hf2', hf4', hf0', ↓reduceIte]
        exact stateOK_setCtrlStack hp wf₂
          ⟨kctx', .letE kt kval kbody, .letE kt kval (kty.abst 0 kctx'.length), hres,
            ⟨max f₁ (max f₂ (max f₃ (max f₄ f₀))) + 1, hinf⟩,
            stackOK_extends (tierExtends_trans ex₁ ex₂) hrest⟩
  | appWhnf _ _ | appDefEq _ _ | lamDomWhnf _ _ _ | forallDomWhnf _ _ _
  | forallBodyWhnf _ | letTyWhnf _ _ _ _ | letValDefEq _ _ _ _ | whnfApp _
  | defEqLhs _ _ | defEqRhs _ _ | defEqSecond _ _ _ =>
    dsimp only [FrameOK] at hfr
    simp only [reduceCtorEq, false_and, exists_false] at hfr

private theorem stepDefEqRhsCells_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} (hp : s.pers = pers) (wf : ScratchColsWF s.scr)
    {fid : Nat} {rest : KontStack} {wa w : EIdx} {c₁ c₂ : ExprCell}
    {ka kb kwa kwb origFid origKa origKb} {f₁ f₂ : Nat}
    (hc₁ : Arena.lookupNode pers s.scr wa = some c₁)
    (hc₂ : Arena.lookupNode pers s.scr w = some c₂)
    (hi₁ : Interprets pers s.scr wa kwa) (hi₂ : Interprets pers s.scr w kwb)
    (hw₁ : whnfFuel env f₁ ka = some kwa) (hw₂ : whnfFuel env f₂ kb = some kwb)
    (htr : (∃ f, defEqSpec env f fid ka kb = true) ->
      ∃ f', defEqSpec env f' origFid origKa origKb = true)
    (hrest : StackOK env pers s.scr (.infer [] rootKE) (.defEq origFid origKa origKb) rest) :
    StateOK env pers rootKE (stepDefEqRhsCells s fid rest c₁ c₂) := by
  have hinv₁ := interprets_invert pers s.scr hi₁ hc₁
  have hinv₂ := interprets_invert pers s.scr hi₂ hc₂
  unfold stepDefEqRhsCells
  cases c₁ <;> cases c₂ <;> dsimp only
  all_goals try exact stateOK_setCtrlStack hp wf ⟨origFid, origKa, origKb, (fun hf => by cases hf), hrest⟩
  · -- bvar, bvar
    dsimp only at hinv₁ hinv₂; subst hinv₁; subst hinv₂
    refine stateOK_setCtrlStack hp wf ⟨origFid, origKa, origKb, ?_, hrest⟩
    intro heq
    exact htr (defEqSpec_of_whnf_leaf hw₁ hw₂ heq)
  · -- fvar, fvar
    dsimp only at hinv₁ hinv₂; subst hinv₁; subst hinv₂
    refine stateOK_setCtrlStack hp wf ⟨origFid, origKa, origKb, ?_, hrest⟩
    intro heq
    exact htr (defEqSpec_of_whnf_leaf hw₁ hw₂ heq)
  · -- sort, sort
    dsimp only at hinv₁ hinv₂; subst hinv₁; subst hinv₂
    refine stateOK_setCtrlStack hp wf ⟨origFid, origKa, origKb, ?_, hrest⟩
    intro heq
    exact htr (defEqSpec_of_whnf_leaf hw₁ hw₂ heq)
  · -- const, const
    dsimp only at hinv₁ hinv₂; subst hinv₁; subst hinv₂
    refine stateOK_setCtrlStack hp wf ⟨origFid, origKa, origKb, ?_, hrest⟩
    intro heq
    exact htr (defEqSpec_of_whnf_leaf hw₁ hw₂ heq)
  · -- app, app
    dsimp only at hinv₁ hinv₂
    rcases hinv₁ with ⟨kf₁, ka₁, rfl, hf₁, ha₁⟩
    rcases hinv₂ with ⟨kf₂, ka₂, rfl, hf₂, ha₂⟩
    refine stateOK_setCtrlStack hp wf
      ⟨kf₁, kf₂, fid, kf₁, kf₂, hf₁, hf₂, (fun h => h),
        ⟨.defEq origFid origKa origKb,
          ⟨fid, kf₁, kf₂, origFid, origKa, origKb, ka₁, ka₂, rfl, rfl, ha₁, ha₂, ?_⟩, hrest⟩⟩
    intro ⟨fa, hfa⟩ ⟨fb, hfb⟩
    exact htr (defEqSpec_of_whnf_pair hw₁ hw₂ (Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hfa hfb)
  · -- lam, lam
    dsimp only at hinv₁ hinv₂
    rcases hinv₁ with ⟨kd₁, kb₁, rfl, hd₁, hb₁⟩
    rcases hinv₂ with ⟨kd₂, kb₂, rfl, hd₂, hb₂⟩
    split
    · next hfid =>
      rw [hp]
      cases ha : allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
      | err c => exact stateOK_failErr hp wf c
      | delegate r => exact stateOK_failDelegate hp wf r
      | ok scr₁ fv =>
        dsimp only
        have ⟨wf₁, hl₁⟩ := allocScr_wf pers wf ha
        have ex₁ := allocScr_extends ha
        have hfv : Interprets pers scr₁ fv (.fvar fid) := by
          have h := interprets_of_lookup pers scr₁ hl₁
          dsimp only at h
          have hn : (UInt32.ofNat fid).toNat = fid := by
            change fid % 4294967296 = fid; omega
          rwa [hn] at h
        cases hi1 : scratchInst s.cfg pers scr₁ s.cfg.maxSteps 0 fv _ with
        | err c => exact stateOK_failErr hp wf c
        | delegate r => exact stateOK_failDelegate hp wf r
        | ok scr₂ b₁' =>
          dsimp only
          have ⟨wf₂, ex₂⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ b₁' wf₁ hi1
          have hb₁' := scratchInst_sound s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ b₁' kb₁ (.fvar fid)
            wf₁ (interprets_extends ex₁ hb₁) hfv hi1
          cases hi2 : scratchInst s.cfg pers scr₂ s.cfg.maxSteps 0 fv _ with
          | err c => exact stateOK_failErr hp wf c
          | delegate r => exact stateOK_failDelegate hp wf r
          | ok scr₃ b₂' =>
            dsimp only
            have ⟨wf₃, ex₃⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps scr₂ scr₃ 0 fv _ b₂' wf₂ hi2
            have hb₂' := scratchInst_sound s.cfg pers s.cfg.maxSteps scr₂ scr₃ 0 fv _ b₂' kb₂ (.fvar fid)
              wf₂ (interprets_extends (tierExtends_trans ex₁ ex₂) hb₂) (interprets_extends ex₂ hfv) hi2
            have ex₁₂₃ := tierExtends_trans ex₁ (tierExtends_trans ex₂ ex₃)
            refine stateOK_setCtrlStack hp wf₃
              ⟨kd₁, kd₂, fid, kd₁, kd₂, interprets_extends ex₁₂₃ hd₁,
                interprets_extends ex₁₂₃ hd₂, (fun h => h),
                ⟨.defEq origFid origKa origKb,
                  ⟨fid, kd₁, kd₂, origFid, origKa, origKb, kb₁.inst 0 (.fvar fid), kb₂.inst 0 (.fvar fid),
                    rfl, rfl, interprets_extends ex₃ hb₁', hb₂', ?_⟩,
                  stackOK_extends ex₁₂₃ hrest⟩⟩
            intro ⟨fa, hfa⟩ ⟨fb, hfb⟩
            exact htr (defEqSpec_of_whnf_pair hw₁ hw₂
              (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) hfa hfb)
    · exact stateOK_failDelegate hp wf .intOverflow
  · -- forallE, forallE
    dsimp only at hinv₁ hinv₂
    rcases hinv₁ with ⟨kd₁, kb₁, rfl, hd₁, hb₁⟩
    rcases hinv₂ with ⟨kd₂, kb₂, rfl, hd₂, hb₂⟩
    split
    · next hfid =>
      rw [hp]
      cases ha : allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
      | err c => exact stateOK_failErr hp wf c
      | delegate r => exact stateOK_failDelegate hp wf r
      | ok scr₁ fv =>
        dsimp only
        have ⟨wf₁, hl₁⟩ := allocScr_wf pers wf ha
        have ex₁ := allocScr_extends ha
        have hfv : Interprets pers scr₁ fv (.fvar fid) := by
          have h := interprets_of_lookup pers scr₁ hl₁
          dsimp only at h
          have hn : (UInt32.ofNat fid).toNat = fid := by
            change fid % 4294967296 = fid; omega
          rwa [hn] at h
        cases hi1 : scratchInst s.cfg pers scr₁ s.cfg.maxSteps 0 fv _ with
        | err c => exact stateOK_failErr hp wf c
        | delegate r => exact stateOK_failDelegate hp wf r
        | ok scr₂ b₁' =>
          dsimp only
          have ⟨wf₂, ex₂⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ b₁' wf₁ hi1
          have hb₁' := scratchInst_sound s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ b₁' kb₁ (.fvar fid)
            wf₁ (interprets_extends ex₁ hb₁) hfv hi1
          cases hi2 : scratchInst s.cfg pers scr₂ s.cfg.maxSteps 0 fv _ with
          | err c => exact stateOK_failErr hp wf c
          | delegate r => exact stateOK_failDelegate hp wf r
          | ok scr₃ b₂' =>
            dsimp only
            have ⟨wf₃, ex₃⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps scr₂ scr₃ 0 fv _ b₂' wf₂ hi2
            have hb₂' := scratchInst_sound s.cfg pers s.cfg.maxSteps scr₂ scr₃ 0 fv _ b₂' kb₂ (.fvar fid)
              wf₂ (interprets_extends (tierExtends_trans ex₁ ex₂) hb₂) (interprets_extends ex₂ hfv) hi2
            have ex₁₂₃ := tierExtends_trans ex₁ (tierExtends_trans ex₂ ex₃)
            refine stateOK_setCtrlStack hp wf₃
              ⟨kd₁, kd₂, fid, kd₁, kd₂, interprets_extends ex₁₂₃ hd₁,
                interprets_extends ex₁₂₃ hd₂, (fun h => h),
                ⟨.defEq origFid origKa origKb,
                  ⟨fid, kd₁, kd₂, origFid, origKa, origKb, kb₁.inst 0 (.fvar fid), kb₂.inst 0 (.fvar fid),
                    rfl, rfl, interprets_extends ex₃ hb₁', hb₂', ?_⟩,
                  stackOK_extends ex₁₂₃ hrest⟩⟩
            intro ⟨fa, hfa⟩ ⟨fb, hfb⟩
            exact htr (defEqSpec_of_whnf_pair hw₁ hw₂
              (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) hfa hfb)
    · exact stateOK_failDelegate hp wf .intOverflow

private theorem stepRetWhnf_whnfApp_nonlam {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} (hp : s.pers = pers) (wf : ScratchColsWF s.scr)
    {rest : KontStack} {w arg : EIdx} {origKe origKe' kw karg : KExpr} {f₀ : Nat}
    (hw : Interprets pers s.scr w kw) (harg : Interprets pers s.scr arg karg)
    (hf₀ : whnfFuel env f₀ origKe = some kw)
    (htr : ∀ kw' f, whnfFuel env f (.app origKe karg) = some kw' ->
      ∃ f', whnfFuel env f' origKe' = some kw')
    (hrest : StackOK env pers s.scr (.infer [] rootKE) (.whnf origKe') rest)
    (hnl : ∀ ty b, kw ≠ .lam ty b) :
    StateOK env pers rootKE
      (match allocScr s.cfg s.scr (.app w arg) with
      | .err c => failErr s c
      | .delegate r => failDelegate s r
      | .ok scr₁ res => setCtrlStack s scr₁ rest (.retWhnf res)) := by
  cases ha : allocScr s.cfg s.scr (.app w arg) with
  | err c => exact stateOK_failErr hp wf c
  | delegate r => exact stateOK_failDelegate hp wf r
  | ok scr₁ res =>
    dsimp only
    have ⟨wf₁, hl₁⟩ := allocScr_wf pers wf ha
    have ex₁ := allocScr_extends ha
    have hres : Interprets pers scr₁ res (.app kw karg) :=
      interprets_of_lookup pers scr₁ hl₁ (interprets_extends ex₁ hw) (interprets_extends ex₁ harg)
    have hstep1 : whnfFuel env (f₀ + 1) (.app origKe karg) = some (.app kw karg) := by
      cases kw with
      | lam ty b => exact absurd rfl (hnl ty b)
      | bvar _ | fvar _ | sort _ | const _ | app _ _ | forallE _ _ | letE _ _ _ =>
        simp [whnfFuel, hf₀]
    obtain ⟨f', hf'⟩ := htr (.app kw karg) (f₀ + 1) hstep1
    exact stateOK_setCtrlStack hp wf₁
      ⟨origKe', .app kw karg, hres, ⟨f', hf'⟩, stackOK_extends ex₁ hrest⟩

theorem stepRetWhnf_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} {s : MachineState}
    (hp : s.pers = pers) (wf : ScratchColsWF s.scr)
    {f : Frame} {rest : KontStack} {w : EIdx}
    (hc : CtrlOK env pers s.scr (.infer [] rootKE) (.retWhnf w) (f :: rest)) :
    StateOK env pers rootKE (stepRetWhnf s f rest w) := by
  rcases hc with ⟨origKe, kw, hw, ⟨f₀, hf₀⟩, ⟨nextGoal, hfr, hrest⟩⟩
  unfold stepRetWhnf
  cases f with
  | appWhnf ctx arg =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx, kfn, karg, kfty, hg1, rfl, hctx, harg, f₁, hf1⟩
    cases hg1
    rw [hp]
    cases hl : Arena.lookupNode pers s.scr w with
    | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
    | some cell =>
      have hinv := interprets_invert pers s.scr hw hl
      cases cell with
      | forallE dom cod =>
        dsimp only
        dsimp only at hinv
        rcases hinv with ⟨kdom, kcod, rfl, hdom, hcod⟩
        exact stateOK_setCtrlStack hp wf
          ⟨kctx, karg, hctx, harg,
            ⟨.infer kctx (.app kfn karg),
              ⟨kctx, kfn, karg, kdom, kcod, rfl, rfl, hctx, harg, hdom, hcod, f₁, f₀, origKe, hf1, hf₀⟩, hrest⟩⟩
      | _ => dsimp only; exact stateOK_failErr hp wf .expectedPi
  | lamDomWhnf ctx dom body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx, kdom, kbody, kdomTy, hg1, rfl, hctx, hdom, hb, f₁, hf1⟩
    cases hg1
    rw [hp]
    cases hl : Arena.lookupNode pers s.scr w with
    | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
    | some cell =>
      have hinv := interprets_invert pers s.scr hw hl
      cases cell with
      | sort lvl =>
        dsimp only
        dsimp only at hinv; subst hinv
        split
        · next hfid =>
          cases ha : allocScr s.cfg s.scr (.fvar (UInt32.ofNat ctx.length)) with
          | err c => exact stateOK_failErr hp wf c
          | delegate r => exact stateOK_failDelegate hp wf r
          | ok scr₁ fv =>
            dsimp only
            have ⟨wf₁, hl₁⟩ := allocScr_wf pers wf ha
            have ex₁ := allocScr_extends ha
            have hfv : Interprets pers scr₁ fv (.fvar ctx.length) := by
              have h := interprets_of_lookup pers scr₁ hl₁
              dsimp only at h
              have hn : (UInt32.ofNat ctx.length).toNat = ctx.length := by
                change ctx.length % 4294967296 = ctx.length; omega
              rwa [hn] at h
            cases hi : scratchInst s.cfg pers scr₁ s.cfg.maxSteps 0 fv body with
            | err c => exact stateOK_failErr hp wf c
            | delegate r => exact stateOK_failDelegate hp wf r
            | ok scr₂ body' =>
              dsimp only
              have ⟨wf₂, ex₂⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv body body' wf₁ hi
              have hb' := scratchInst_sound s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv body body' kbody (.fvar ctx.length)
                wf₁ (interprets_extends ex₁ hb) hfv hi
              have ex₁₂ := tierExtends_trans ex₁ ex₂
              have hdom₂ := interprets_extends ex₁₂ hdom
              have hctx₂ := interpretsCtx_snoc (interpretsCtx_extends ex₁₂ hctx) hdom₂
              exact stateOK_setCtrlStack hp wf₂
                ⟨kctx ++ [kdom], kbody.inst 0 (.fvar ctx.length), hctx₂, hb',
                  ⟨.infer kctx (.lam kdom kbody),
                    ⟨kctx, kdom, kbody, origKe, lvl.toNat, hctx.1, by rw [hctx.1], rfl, hdom₂, f₁, f₀, hf1, hf₀⟩,
                    stackOK_extends ex₁₂ hrest⟩⟩
        · exact stateOK_failDelegate hp wf .intOverflow
      | _ => dsimp only; exact stateOK_failErr hp wf .expectedSort
  | forallDomWhnf ctx dom body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx, kdom, kbody, kdomTy, hg1, rfl, hctx, hdom, hb, f₁, hf1⟩
    cases hg1
    rw [hp]
    cases hl : Arena.lookupNode pers s.scr w with
    | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
    | some cell =>
      have hinv := interprets_invert pers s.scr hw hl
      cases cell with
      | sort u =>
        dsimp only
        dsimp only at hinv; subst hinv
        split
        · next hfid =>
          cases ha : allocScr s.cfg s.scr (.fvar (UInt32.ofNat ctx.length)) with
          | err c => exact stateOK_failErr hp wf c
          | delegate r => exact stateOK_failDelegate hp wf r
          | ok scr₁ fv =>
            dsimp only
            have ⟨wf₁, hl₁⟩ := allocScr_wf pers wf ha
            have ex₁ := allocScr_extends ha
            have hfv : Interprets pers scr₁ fv (.fvar ctx.length) := by
              have h := interprets_of_lookup pers scr₁ hl₁
              dsimp only at h
              have hn : (UInt32.ofNat ctx.length).toNat = ctx.length := by
                change ctx.length % 4294967296 = ctx.length; omega
              rwa [hn] at h
            cases hi : scratchInst s.cfg pers scr₁ s.cfg.maxSteps 0 fv body with
            | err c => exact stateOK_failErr hp wf c
            | delegate r => exact stateOK_failDelegate hp wf r
            | ok scr₂ body' =>
              dsimp only
              have ⟨wf₂, ex₂⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv body body' wf₁ hi
              have hb' := scratchInst_sound s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv body body' kbody (.fvar ctx.length)
                wf₁ (interprets_extends ex₁ hb) hfv hi
              have ex₁₂ := tierExtends_trans ex₁ ex₂
              have hdom₂ := interprets_extends ex₁₂ hdom
              have hctx₂ := interpretsCtx_snoc (interpretsCtx_extends ex₁₂ hctx) hdom₂
              exact stateOK_setCtrlStack hp wf₂
                ⟨kctx ++ [kdom], kbody.inst 0 (.fvar ctx.length), hctx₂, hb',
                  ⟨.infer kctx (.forallE kdom kbody),
                    ⟨kctx, kdom, kbody, origKe, by rw [hctx.1], rfl, f₁, f₀, hf1, hf₀⟩,
                    stackOK_extends ex₁₂ hrest⟩⟩
        · exact stateOK_failDelegate hp wf .intOverflow
      | _ => dsimp only; exact stateOK_failErr hp wf .expectedSort
  | forallBodyWhnf u =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx, kdom, kbody, kdomTy, kbodyTy, hg1, rfl, f₁, f₂, f₃, hf1, hf2, hf3⟩
    cases hg1
    rw [hp]
    cases hl : Arena.lookupNode pers s.scr w with
    | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
    | some cell =>
      have hinv := interprets_invert pers s.scr hw hl
      cases cell with
      | sort v =>
        dsimp only
        dsimp only at hinv; subst hinv
        cases ha : allocScr s.cfg s.scr (.sort (UInt32.ofNat (imax u.toNat v.toNat))) with
        | err c => exact stateOK_failErr hp wf c
        | delegate r => exact stateOK_failDelegate hp wf r
        | ok scr₁ res =>
          dsimp only
          have ⟨wf₁, hl₁⟩ := allocScr_wf pers wf ha
          have ex₁ := allocScr_extends ha
          have hlook : Interprets pers scr₁ res (.sort (UInt32.ofNat (imax u.toNat v.toNat)).toNat) := by
            have h := interprets_of_lookup pers scr₁ hl₁
            dsimp only at h
            exact h
          have hlt : imax u.toNat v.toNat < 4294967296 := by
            unfold imax
            have hu := u.toNat_lt
            have hv := v.toNat_lt
            split <;> omega
          have hnat : (UInt32.ofNat (imax u.toNat v.toNat)).toNat = imax u.toNat v.toNat := by
            change imax u.toNat v.toNat % 4294967296 = imax u.toNat v.toNat; omega
          rw [hnat] at hlook
          have hf1' := inferSpec_mono env (by omega : f₁ ≤ max f₁ (max f₂ (max f₃ f₀))) _ _ _ hf1
          have hf2' := whnfFuel_mono env (by omega : f₂ ≤ max f₁ (max f₂ (max f₃ f₀))) _ _ hf2
          have hf3' := inferSpec_mono env (by omega : f₃ ≤ max f₁ (max f₂ (max f₃ f₀))) _ _ _ hf3
          have hf0' := whnfFuel_mono env (by omega : f₀ ≤ max f₁ (max f₂ (max f₃ f₀))) _ _ hf₀
          have hinf : inferSpec env (max f₁ (max f₂ (max f₃ f₀)) + 1) kctx (.forallE kdom kbody) =
              some (.sort (imax u.toNat v.toNat)) := by
            simp only [inferSpec, hf1', hf2', hf3', hf0']
          exact stateOK_setCtrlStack hp wf₁
            ⟨kctx, .forallE kdom kbody, .sort (imax u.toNat v.toNat), hlook,
              ⟨max f₁ (max f₂ (max f₃ f₀)) + 1, hinf⟩, stackOK_extends ex₁ hrest⟩
      | _ => dsimp only; exact stateOK_failErr hp wf .expectedSort
  | letTyWhnf ctx ty val body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx, kty, kval, kbody, ktyTy, hg1, rfl, hctx, hty, hval, hb, f₁, hf1⟩
    cases hg1
    rw [hp]
    cases hl : Arena.lookupNode pers s.scr w with
    | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
    | some cell =>
      have hinv := interprets_invert pers s.scr hw hl
      cases cell with
      | sort u =>
        dsimp only
        dsimp only at hinv; subst hinv
        exact stateOK_setCtrlStack hp wf
          ⟨kctx, kval, hctx, hval,
            ⟨.infer kctx (.letE kty kval kbody),
              ⟨kctx, kty, kval, kbody, origKe, u.toNat, rfl, rfl, hctx, hty, hval, hb, f₁, f₀, hf1, hf₀⟩, hrest⟩⟩
      | _ => dsimp only; exact stateOK_failErr hp wf .expectedSort
  | whnfApp arg =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kfn, karg, origKe', hg1, rfl, harg, htr⟩
    cases hg1
    rw [hp]
    cases hl : Arena.lookupNode pers s.scr w with
    | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
    | some cell =>
      have hinv := interprets_invert pers s.scr hw hl
      cases cell with
      | lam ldom lbody =>
        dsimp only
        dsimp only at hinv
        rcases hinv with ⟨kldom, klb, rfl, _, hlb⟩
        cases hi : scratchInst s.cfg pers s.scr s.cfg.maxSteps 0 arg lbody with
        | err c => exact stateOK_failErr hp wf c
        | delegate r => exact stateOK_failDelegate hp wf r
        | ok scr₁ body' =>
          dsimp only
          have ⟨wf₁, ex₁⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 arg lbody body' wf hi
          have hsound := scratchInst_sound s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 arg lbody body' klb karg
            wf hlb harg hi
          refine stateOK_setCtrlStack hp wf₁ ⟨klb.inst 0 karg, origKe', hsound, ?_, stackOK_extends ex₁ hrest⟩
          intro kw f hwf
          apply htr kw (max f₀ f + 1)
          have hf0' := whnfFuel_mono env (Nat.le_max_left f₀ f) _ _ hf₀
          have hwf' := whnfFuel_mono env (Nat.le_max_right f₀ f) _ _ hwf
          simp only [whnfFuel, hf0']
          exact hwf'
      | bvar _ =>
        dsimp only; dsimp only at hinv
        exact stepRetWhnf_whnfApp_nonlam hp wf hw harg hf₀ htr hrest (by subst hinv; intro _ _ h; cases h)
      | fvar _ =>
        dsimp only; dsimp only at hinv
        exact stepRetWhnf_whnfApp_nonlam hp wf hw harg hf₀ htr hrest (by subst hinv; intro _ _ h; cases h)
      | sort _ =>
        dsimp only; dsimp only at hinv
        exact stepRetWhnf_whnfApp_nonlam hp wf hw harg hf₀ htr hrest (by subst hinv; intro _ _ h; cases h)
      | const _ =>
        dsimp only; dsimp only at hinv
        exact stepRetWhnf_whnfApp_nonlam hp wf hw harg hf₀ htr hrest (by subst hinv; intro _ _ h; cases h)
      | app _ _ =>
        dsimp only; dsimp only at hinv
        exact stepRetWhnf_whnfApp_nonlam hp wf hw harg hf₀ htr hrest
          (by rcases hinv with ⟨_, _, rfl, _⟩; intro _ _ h; cases h)
      | forallE _ _ =>
        dsimp only; dsimp only at hinv
        exact stepRetWhnf_whnfApp_nonlam hp wf hw harg hf₀ htr hrest
          (by rcases hinv with ⟨_, _, rfl, _⟩; intro _ _ h; cases h)
      | letE _ _ _ =>
        dsimp only; dsimp only at hinv
        exact stepRetWhnf_whnfApp_nonlam hp wf hw harg hf₀ htr hrest
          (by rcases hinv with ⟨_, _, _, rfl, _⟩; intro _ _ h; cases h)
  | defEqLhs fid b =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨ka, kb, origFid, origKa, origKb, hg1, rfl, hb, htr⟩
    cases hg1
    exact stateOK_setCtrlStack hp wf
      ⟨kb, kb, hb, (fun _ f h => ⟨f, h⟩),
        ⟨.defEq origFid origKa origKb,
          ⟨origKe, kb, kw, origFid, origKa, origKb, rfl, rfl, hw, ⟨f₀, hf₀⟩, htr⟩, hrest⟩⟩
  | defEqRhs fid wa =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨ka, kb, kwa, origFid, origKa, origKb, hg1, rfl, hwa, ⟨f₁, hf1⟩, htr⟩
    cases hg1
    rw [hp]
    cases hl1 : Arena.lookupNode pers s.scr wa with
    | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
    | some c₁ =>
      cases hl2 : Arena.lookupNode pers s.scr w with
      | none => dsimp only; exact stateOK_failErr hp wf .danglingHandle
      | some c₂ =>
        dsimp only
        exact stepDefEqRhsCells_ok hp wf hl1 hl2 hwa hw hf1 hf₀ htr hrest
  | appFn _ _ | appArg _ _ _ _ | appDefEq _ _ | lamDom _ _ _ | lamBody _ _
  | forallDom _ _ _ | forallBody _ | letTy _ _ _ _ | letVal _ _ _ _
  | letValDefEq _ _ _ _ | letBody _ _ _ | defEqSecond _ _ _ =>
    dsimp only [FrameOK] at hfr
    simp at hfr

theorem stepRetDefEq_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} {s : MachineState}
    (hp : s.pers = pers) (wf : ScratchColsWF s.scr)
    {f : Frame} {rest : KontStack} {ok : Bool}
    (hc : CtrlOK env pers s.scr (.infer [] rootKE) (.retDefEq ok) (f :: rest)) :
    StateOK env pers rootKE (stepRetDefEq s f rest ok) := by
  rcases hc with ⟨origFid, origKa, origKb, hok, ⟨nextGoal, hfr, hrest⟩⟩
  unfold stepRetDefEq
  cases f with
  | appDefEq cod arg =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx, kfn, karg, kdom, kcod, katy, hg1, rfl, hcod, harg, f₁, f₂, f₃, kfty, hf1, hf2, hf3⟩
    cases hg1
    by_cases hokb : ok = true
    · subst hokb
      simp only [↓reduceIte]
      obtain ⟨f₄, hf4⟩ := hok rfl
      rw [hp]
      cases hi : scratchInst s.cfg pers s.scr s.cfg.maxSteps 0 arg cod with
      | err c => exact stateOK_failErr hp wf c
      | delegate r => exact stateOK_failDelegate hp wf r
      | ok scr₁ res =>
        dsimp only
        have ⟨wf₁, ex₁⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 arg cod res wf hi
        have hsound := scratchInst_sound s.cfg pers s.cfg.maxSteps s.scr scr₁ 0 arg cod res kcod karg wf hcod harg hi
        have hf1' := inferSpec_mono env (by omega : f₁ ≤ max f₁ (max f₂ (max f₃ f₄))) _ _ _ hf1
        have hf2' := whnfFuel_mono env (by omega : f₂ ≤ max f₁ (max f₂ (max f₃ f₄))) _ _ hf2
        have hf3' := inferSpec_mono env (by omega : f₃ ≤ max f₁ (max f₂ (max f₃ f₄))) _ _ _ hf3
        have hf4' := defEqSpec_mono env (by omega : f₄ ≤ max f₁ (max f₂ (max f₃ f₄))) _ _ _ hf4
        have hinf : inferSpec env (max f₁ (max f₂ (max f₃ f₄)) + 1) kctx (.app kfn karg) =
            some (kcod.inst 0 karg) := by
          simp only [inferSpec, hf1', hf3', hf2', hf4', ↓reduceIte]
        exact stateOK_setCtrlStack hp wf₁
          ⟨kctx, .app kfn karg, kcod.inst 0 karg, hsound, ⟨max f₁ (max f₂ (max f₃ f₄)) + 1, hinf⟩,
            stackOK_extends ex₁ hrest⟩
    · simp only [hokb]
      exact stateOK_failErr hp wf .appTypeMismatch
  | letValDefEq ctx ty val body =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨kctx, kty, kval, kbody, ktyTy, kvalTy, u, hg1, rfl, hctx, hty, hval, hb, f₁, f₂, f₃, hf1, hf2, hf3⟩
    cases hg1
    by_cases hokb : ok = true
    · subst hokb
      simp only [↓reduceIte]
      obtain ⟨f₄, hf4⟩ := hok rfl
      split
      · next hfid =>
        rw [hp]
        cases ha : allocScr s.cfg s.scr (.fvar (UInt32.ofNat ctx.length)) with
        | err c => exact stateOK_failErr hp wf c
        | delegate r => exact stateOK_failDelegate hp wf r
        | ok scr₁ fv =>
          dsimp only
          have ⟨wf₁, hl₁⟩ := allocScr_wf pers wf ha
          have ex₁ := allocScr_extends ha
          have hfv : Interprets pers scr₁ fv (.fvar ctx.length) := by
            have h := interprets_of_lookup pers scr₁ hl₁
            dsimp only at h
            have hn : (UInt32.ofNat ctx.length).toNat = ctx.length := by
              change ctx.length % 4294967296 = ctx.length; omega
            rwa [hn] at h
          cases hi : scratchInst s.cfg pers scr₁ s.cfg.maxSteps 0 fv body with
          | err c => exact stateOK_failErr hp wf c
          | delegate r => exact stateOK_failDelegate hp wf r
          | ok scr₂ body' =>
            dsimp only
            have ⟨wf₂, ex₂⟩ := scratchInst_extends s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv body body' wf₁ hi
            have hb' := scratchInst_sound s.cfg pers s.cfg.maxSteps scr₁ scr₂ 0 fv body body' kbody (.fvar ctx.length)
              wf₁ (interprets_extends ex₁ hb) hfv hi
            have ex₁₂ := tierExtends_trans ex₁ ex₂
            have hty₂ := interprets_extends ex₁₂ hty
            have hval₂ := interprets_extends ex₁₂ hval
            have hctx₂ := interpretsCtx_snoc (interpretsCtx_extends ex₁₂ hctx) hty₂
            exact stateOK_setCtrlStack hp wf₂
              ⟨kctx ++ [origKb], kbody.inst 0 (.fvar ctx.length), hctx₂, hb',
                ⟨.infer kctx (.letE origKb kval kbody),
                  ⟨kctx, origKb, kval, kbody, ktyTy, origKa, u, hctx.1, by rw [hctx.1], rfl,
                    hty₂, hval₂, f₁, f₂, f₃, f₄, hf1, hf2, hf3, by rw [hctx.1]; exact hf4⟩,
                  stackOK_extends ex₁₂ hrest⟩⟩
      · exact stateOK_failDelegate hp wf .intOverflow
    · simp only [hokb]
      exact stateOK_failErr hp wf .letTypeMismatch
  | defEqSecond fid₂ e₁ e₂ =>
    dsimp only
    dsimp only [FrameOK] at hfr
    rcases hfr with ⟨fid₁, x₁, x₂, origFid', origKa', origKb', y₁, y₂, hg1, rfl, he1, he2, hcomb⟩
    cases hg1
    by_cases hokb : ok = true
    · subst hokb
      simp only [↓reduceIte]
      have hfirst := hok rfl
      exact stateOK_setCtrlStack hp wf ⟨y₁, y₂, origFid', origKa', origKb', he1, he2, hcomb hfirst, hrest⟩
    · simp only [hokb]
      exact stateOK_setCtrlStack hp wf ⟨origFid', origKa', origKb', (fun h => by cases h), hrest⟩
  | appFn _ _ | appWhnf _ _ | appArg _ _ _ _ | lamDom _ _ _ | lamDomWhnf _ _ _
  | lamBody _ _ | forallDom _ _ _ | forallDomWhnf _ _ _ | forallBody _ | forallBodyWhnf _
  | letTy _ _ _ _ | letTyWhnf _ _ _ _ | letVal _ _ _ _ | letBody _ _ _
  | whnfApp _ | defEqLhs _ _ | defEqRhs _ _ =>
    dsimp only [FrameOK] at hfr
    simp at hfr

theorem step_preserves_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {s : MachineState} (henv : EnvSound pers s.gpuEnv env)
    (hs : StateOK env pers rootKE s) :
    StateOK env pers rootKE (step s) := by
  unfold step
  by_cases hrun : s.status = .running
  · simp only [hrun, ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases hlim : s.cfg.maxSteps ≤ s.stepsUsed
    · simp only [hlim, ↓reduceIte]
      exact ⟨hs.1, hs.2.1, (fun h => by cases h), (fun _ h => by cases h)⟩
    · simp only [hlim, ↓reduceIte]
      have hctrl := hs.2.2.1 hrun
      cases hc : s.ctrl with
      | evalInfer ctx e =>
        rw [hc] at hctrl
        exact stepEvalInfer_ok hs.1 hs.2.1 henv hctrl
      | evalWhnf e =>
        rw [hc] at hctrl
        exact stepEvalWhnf_ok hs.1 hs.2.1 henv hctrl
      | evalDefEq fid a b =>
        rw [hc] at hctrl
        exact stepEvalDefEq_ok hs.1 hs.2.1 hctrl
      | retInfer ty =>
        rw [hc] at hctrl
        cases hstk : s.stack with
        | nil =>
          rw [hstk] at hctrl
          rcases hctrl with ⟨kctx, ke, kty, hty, hinf, hempty⟩
          have heq : SubGoal.infer kctx ke = SubGoal.infer [] rootKE := hempty
          cases heq
          refine ⟨hs.1, hs.2.1, (fun h => by cases h), ?_⟩
          intro ty' hok
          simp only [finishOk, MachineStatus.ok.injEq] at hok
          subst hok
          exact ⟨kty, hty, hinf⟩
        | cons f rest =>
          rw [hstk] at hctrl
          exact stepRetInfer_ok hs.1 hs.2.1 hctrl
      | retWhnf w =>
        rw [hc] at hctrl
        cases hstk : s.stack with
        | nil =>
          rw [hstk] at hctrl
          rcases hctrl with ⟨_, _, _, _, hempty⟩
          cases hempty
        | cons f rest =>
          rw [hstk] at hctrl
          exact stepRetWhnf_ok hs.1 hs.2.1 hctrl
      | retDefEq ok =>
        rw [hc] at hctrl
        cases hstk : s.stack with
        | nil =>
          rw [hstk] at hctrl
          rcases hctrl with ⟨_, _, _, _, hempty⟩
          cases hempty
        | cons f rest =>
          rw [hstk] at hctrl
          exact stepRetDefEq_ok hs.1 hs.2.1 hctrl
  · simp only [hrun, ne_eq, not_false_eq_true, ↓reduceIte]
    exact hs

private theorem goCtrl_gpuEnv (s : MachineState) (scr' : SoATier) (c : Control) :
    (goCtrl s scr' c).gpuEnv = s.gpuEnv := rfl

private theorem setCtrlStack_gpuEnv (s : MachineState) (scr' : SoATier) (st : KontStack) (c : Control) :
    (setCtrlStack s scr' st c).gpuEnv = s.gpuEnv := rfl

private theorem pushFrame_gpuEnv (s : MachineState) (scr' : SoATier) (f : Frame) (c : Control) :
    (pushFrame s scr' f c).gpuEnv = s.gpuEnv := by
  unfold pushFrame; split <;> rfl

private theorem failErr_gpuEnv (s : MachineState) (c : ErrCode) :
    (failErr s c).gpuEnv = s.gpuEnv := rfl

private theorem failDelegate_gpuEnv (s : MachineState) (r : DelegateReason) :
    (failDelegate s r).gpuEnv = s.gpuEnv := rfl

private theorem finishOk_gpuEnv (s : MachineState) (ty : EIdx) :
    (finishOk s ty).gpuEnv = s.gpuEnv := rfl

private theorem stepEvalInfer_gpuEnv (s : MachineState) (ctx : List EIdx) (e : EIdx) :
    (stepEvalInfer s ctx e).gpuEnv = s.gpuEnv := by
  unfold stepEvalInfer
  rcases Arena.lookupNode s.pers s.scr e with _ | cell
  · rfl
  · cases cell <;> dsimp only <;>
      repeat first | rfl | exact failErr_gpuEnv .. | exact failDelegate_gpuEnv .. |
        exact goCtrl_gpuEnv .. | exact pushFrame_gpuEnv .. | split

private theorem stepEvalWhnf_gpuEnv (s : MachineState) (e : EIdx) :
    (stepEvalWhnf s e).gpuEnv = s.gpuEnv := by
  unfold stepEvalWhnf
  rcases Arena.lookupNode s.pers s.scr e with _ | cell
  · rfl
  · cases cell <;> dsimp only <;>
      repeat first | rfl | exact failErr_gpuEnv .. | exact failDelegate_gpuEnv .. |
        exact goCtrl_gpuEnv .. | exact pushFrame_gpuEnv .. | split

private theorem stepEvalDefEq_gpuEnv (s : MachineState) (fid : Nat) (a b : EIdx) :
    (stepEvalDefEq s fid a b).gpuEnv = s.gpuEnv := by
  unfold stepEvalDefEq
  split
  · rfl
  · exact pushFrame_gpuEnv s s.scr (.defEqLhs fid b) (.evalWhnf a)

private theorem stepDefEqRhsCells_gpuEnv (s : MachineState) (fid : Nat) (rest : KontStack)
    (c₁ c₂ : ExprCell) : (stepDefEqRhsCells s fid rest c₁ c₂).gpuEnv = s.gpuEnv := by
  unfold stepDefEqRhsCells
  cases c₁ <;> cases c₂ <;> dsimp only <;>
    repeat first | rfl | exact setCtrlStack_gpuEnv .. | exact failErr_gpuEnv .. |
      exact failDelegate_gpuEnv .. | split

private theorem stepRetInfer_gpuEnv (s : MachineState) (f : Frame) (rest : KontStack) (ty : EIdx) :
    (stepRetInfer s f rest ty).gpuEnv = s.gpuEnv := by
  unfold stepRetInfer
  cases f <;> dsimp only <;>
    repeat first | rfl | exact setCtrlStack_gpuEnv .. | exact failErr_gpuEnv .. |
      exact failDelegate_gpuEnv .. | split

private theorem stepRetWhnf_gpuEnv (s : MachineState) (f : Frame) (rest : KontStack) (w : EIdx) :
    (stepRetWhnf s f rest w).gpuEnv = s.gpuEnv := by
  unfold stepRetWhnf
  cases f with
  | defEqLhs _ _ => exact setCtrlStack_gpuEnv ..
  | defEqRhs fid wa =>
    dsimp only
    rcases Arena.lookupNode s.pers s.scr wa with _ | c₁
    · rfl
    · rcases Arena.lookupNode s.pers s.scr w with _ | c₂
      · rfl
      · exact stepDefEqRhsCells_gpuEnv s fid rest c₁ c₂
  | appWhnf _ _ | lamDomWhnf _ _ _ | forallDomWhnf _ _ _ | forallBodyWhnf _ | letTyWhnf _ _ _ _
  | whnfApp _ | appFn _ _ | appArg _ _ _ _ | appDefEq _ _ | lamDom _ _ _ | lamBody _ _
  | forallDom _ _ _ | forallBody _ | letTy _ _ _ _ | letVal _ _ _ _ | letValDefEq _ _ _ _
  | letBody _ _ _ | defEqSecond _ _ _ =>
    dsimp only
    repeat first | rfl | exact setCtrlStack_gpuEnv .. | exact failErr_gpuEnv .. |
      exact failDelegate_gpuEnv .. | split

private theorem stepRetDefEq_gpuEnv (s : MachineState) (f : Frame) (rest : KontStack) (ok : Bool) :
    (stepRetDefEq s f rest ok).gpuEnv = s.gpuEnv := by
  unfold stepRetDefEq
  cases f <;> dsimp only <;>
    repeat first | rfl | exact setCtrlStack_gpuEnv .. | exact failErr_gpuEnv .. |
      exact failDelegate_gpuEnv .. | split

private theorem step_preserves_gpuEnv (s : MachineState) :
    (step s).gpuEnv = s.gpuEnv := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · cases s.ctrl with
      | evalInfer ctx e => exact stepEvalInfer_gpuEnv s ctx e
      | evalWhnf e => exact stepEvalWhnf_gpuEnv s e
      | evalDefEq fid a b => exact stepEvalDefEq_gpuEnv s fid a b
      | retInfer ty =>
        cases s.stack with
        | nil => rfl
        | cons f rest => exact stepRetInfer_gpuEnv s f rest ty
      | retWhnf w =>
        cases s.stack with
        | nil => rfl
        | cons f rest => exact stepRetWhnf_gpuEnv s f rest w
      | retDefEq ok =>
        cases s.stack with
        | nil => rfl
        | cons f rest => exact stepRetDefEq_gpuEnv s f rest ok

theorem runMachine_preserves_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} :
    ∀ (n : Nat) (s : MachineState),
      EnvSound pers s.gpuEnv env ->
      StateOK env pers rootKE s ->
      StateOK env pers rootKE (runMachine n s) ∧ (runMachine n s).gpuEnv = s.gpuEnv
  | 0, s, _, hs => ⟨hs, rfl⟩
  | n + 1, s, henv, hs => by
    have hs1 := step_preserves_ok henv hs
    have hge1 := step_preserves_gpuEnv s
    have henv1 : EnvSound pers (step s).gpuEnv env := by rw [hge1]; exact henv
    obtain ⟨hs2, hge2⟩ := runMachine_preserves_ok n (step s) henv1 hs1
    exact ⟨hs2, by simp only [runMachine, hge2, hge1]⟩

/-! ### 6. Main Theorem: Soundness of Bounded Stackless GPU Typechecking (`stepMachine_sound`) -/

theorem initInfer_stateOK {cfg : MachineLimits} {gpuEnv : Array GpuConstDecl}
    {pers : SoATier} {e : EIdx} {ke : KExpr}
    (he : Interprets pers .empty e ke) :
    ∀ {env : KEnv}, StateOK env pers ke (initInfer cfg gpuEnv pers e) := by
  intro env
  refine ⟨rfl, scratchColsWF_empty, ?_, fun _ h => by cases h⟩
  intro _
  exact ⟨[], ke, interpretsCtx_nil pers .empty, he, rfl⟩

/-- If `runSteps n (initInfer cfg gpuEnv pers e) = .ok ty`, then `ty` decodes to a type
    `kty` validated by the declarative recursive kernel specification `inferSpec`. -/
theorem stepMachine_sound {cfg : MachineLimits} {gpuEnv : Array GpuConstDecl}
    {pers : SoATier} {env : KEnv} {n : Nat} {e ty : EIdx} {ke : KExpr}
    (henv : EnvSound pers gpuEnv env)
    (he : Interprets pers .empty e ke)
    (hok : runSteps n (initInfer cfg gpuEnv pers e) = .ok ty) :
    ∃ kty, Interprets pers (runMachine n (initInfer cfg gpuEnv pers e)).scr ty kty ∧
      ∃ fuel, inferSpec env fuel [] ke = some kty := by
  have hinit : StateOK env pers ke (initInfer cfg gpuEnv pers e) := initInfer_stateOK he
  have hrun := (runMachine_preserves_ok n (initInfer cfg gpuEnv pers e) henv hinit).1
  exact hrun.2.2.2 ty hok

/-- Corollary linking accepted GPU typechecking directly to the declarative typing judgment `HasType`. -/
theorem stepMachine_hasType {cfg : MachineLimits} {gpuEnv : Array GpuConstDecl}
    {pers : SoATier} {env : KEnv} {n : Nat} {e ty : EIdx} {ke : KExpr}
    (henv : EnvSound pers gpuEnv env)
    (he : Interprets pers .empty e ke)
    (hok : runSteps n (initInfer cfg gpuEnv pers e) = .ok ty) :
    ∃ kty, Interprets pers (runMachine n (initInfer cfg gpuEnv pers e)).scr ty kty ∧
      HasType env [] ke kty := by
  obtain ⟨kty, hty, fuel, hinf⟩ := stepMachine_sound henv he hok
  exact ⟨kty, hty, inferSpec_hasType env fuel [] ke kty hinf⟩

/-! ### 7. Time-Sliced Multi-Quantum Execution & Active-Worklist Compaction Equivalence -/

/-- Execute one time-slice quantum of `q` steps on a single lane, skipping
    lanes whose status is already non-`.running`. -/
def runQuantum (q : Nat) (s : MachineState) : MachineState :=
  if s.status = .running then runMachine q s else s

theorem runQuantum_eq_runMachine (q : Nat) (s : MachineState) :
    runQuantum q s = runMachine q s := by
  unfold runQuantum
  split
  · rfl
  · next hnr => exact (runMachine_nonrunning q hnr).symm

/-- Execute `k` sequential quanta of `q` steps each. -/
def runQuanta : Nat -> Nat -> MachineState -> MachineState
  | 0, _, s => s
  | k + 1, q, s => runQuanta k q (runQuantum q s)

theorem runQuanta_eq_runMachine (k q : Nat) (s : MachineState) :
    runQuanta k q s = runMachine (k * q) s := by
  induction k generalizing s with
  | zero => simp [runQuanta, runMachine]
  | succ k ih =>
    simp only [runQuanta]
    rw [runQuantum_eq_runMachine, ih, ← runMachine_add q (k * q) s, Nat.succ_mul, Nat.add_comm]

theorem runQuanta_sound {cfg : MachineLimits} {gpuEnv : Array GpuConstDecl}
    {pers : SoATier} {env : KEnv} {k q : Nat} {e : EIdx} {ke : KExpr}
    (henv : EnvSound pers gpuEnv env)
    (he : Interprets pers .empty e ke) :
    let s0 := initInfer cfg gpuEnv pers e
    let sk := runQuanta k q s0
    sk.status = runSteps (k * q) s0 ∧
    (∀ r m, m ≤ k -> (runQuanta m q s0).status = .delegate r ->
      ∀ ty, sk.status = .delegate r ∧ sk.status ≠ .ok ty) ∧
    (∀ ty, sk.status = .ok ty ->
      ∃ kty, Interprets pers sk.scr ty kty ∧ HasType env [] ke kty) := by
  intro s0 sk
  have hsk : sk = runMachine (k * q) s0 := runQuanta_eq_runMachine k q s0
  refine ⟨?_, ?_, ?_⟩
  · simp [sk, runSteps, hsk]
  · intro r m hm hdel ty
    have hm' : m * q ≤ k * q := Nat.mul_le_mul_right q hm
    have hdm : (runMachine (m * q) s0).status = .delegate r := by
      rw [← runQuanta_eq_runMachine m q s0]
      exact hdel
    have hmon := runSteps_delegate_monotonic (ty := ty) hm' hdm
    simpa [sk, runSteps, hsk] using hmon
  · intro ty hok
    have hok' : runSteps (k * q) s0 = .ok ty := by
      unfold runSteps
      rw [← hsk]
      exact hok
    obtain ⟨kty, hty, hhas⟩ := stepMachine_hasType henv he hok'
    exact ⟨kty, by simpa [sk, hsk] using hty, hhas⟩

/-- Active-worklist entry pairing a logical job index with its stationary
    backing state slot (`scr`/stack stay fixed at `stateSlot`). -/
structure WorkEntry where
  jobIdx : Nat
  stateSlot : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Injective assignment from job indices `< numJobs` to stationary state slots `< slotsSize`. -/
structure SlotMapWF (numJobs : Nat) (slotOf : Nat -> Nat) (slotsSize : Nat) : Prop where
  inBounds : ∀ j, j < numJobs -> slotOf j < slotsSize
  injective : ∀ j₁ j₂, j₁ < numJobs -> j₂ < numJobs -> slotOf j₁ = slotOf j₂ -> j₁ = j₂

/-- Host-compacted active worklist invariant:
    1. Every entry names a valid job index mapped to `slotOf w.jobIdx`.
    2. State slots in the compacted worklist are duplicate-free (injective compaction).
    3. Every job whose slot is still `.running` appears in the worklist (only
       finished/non-`.running` lanes may be retired). -/
structure CompactedWorklistWF (numJobs : Nat) (slotOf : Nat -> Nat)
    (slots : Array MachineState) (wl : List WorkEntry) : Prop where
  entriesValid : ∀ w ∈ wl, w.jobIdx < numJobs ∧ w.stateSlot = slotOf w.jobIdx
  slotsNodup : (wl.map WorkEntry.stateSlot).Nodup
  activeComplete : ∀ j, j < numJobs -> ∀ hb : slotOf j < slots.size,
    slots[slotOf j].status = .running ->
    slotOf j ∈ wl.map WorkEntry.stateSlot

private theorem nodup_filterMap_inj {α β : Type} (f : α -> Option β) :
    ∀ (l : List α),
      l.Nodup ->
      (∀ a₁ ∈ l, ∀ a₂ ∈ l, ∀ b, f a₁ = some b -> f a₂ = some b -> a₁ = a₂) ->
      (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    have hinj' : ∀ a₁ ∈ xs, ∀ a₂ ∈ xs, ∀ b, f a₁ = some b -> f a₂ = some b -> a₁ = a₂ :=
      fun a₁ h1 a₂ h2 b hf1 hf2 =>
        hinj a₁ (List.mem_cons_of_mem x h1) a₂ (List.mem_cons_of_mem x h2) b hf1 hf2
    have ih := nodup_filterMap_inj f xs hnd.2 hinj'
    cases hfx : f x with
    | none =>
      simp only [List.filterMap_cons, hfx]
      exact ih
    | some b =>
      simp only [List.filterMap_cons, hfx]
      rw [List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      rcases List.mem_filterMap.mp hmem with ⟨x', hx', hfx'⟩
      have heq := hinj x (List.mem_cons_self ..) x' (List.mem_cons_of_mem x hx') b hfx hfx'
      subst heq
      exact hnd.1 hx'

/-- Canonical host-side compaction pass retiring finished (`status ≠ .running`)
    lanes and compacting active `(jobIdx, slotOf jobIdx)` entries in order. -/
def compactActiveWorklist (numJobs : Nat) (slotOf : Nat -> Nat)
    (slots : Array MachineState) : List WorkEntry :=
  (List.range numJobs).filterMap fun j =>
    if h : slotOf j < slots.size then
      if slots[slotOf j].status == .running then
        some ⟨j, slotOf j⟩
      else
        none
    else
      none

theorem compactActiveWorklist_wf {numJobs : Nat} {slotOf : Nat -> Nat}
    {slots : Array MachineState} (hs : SlotMapWF numJobs slotOf slots.size) :
    CompactedWorklistWF numJobs slotOf slots (compactActiveWorklist numJobs slotOf slots) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    unfold compactActiveWorklist at hw
    rcases List.mem_filterMap.mp hw with ⟨j, hj, hres⟩
    rw [List.mem_range] at hj
    split at hres
    · split at hres
      · simp only [Option.some.injEq] at hres
        rw [← hres]
        exact ⟨hj, rfl⟩
      · cases hres
    · cases hres
  · unfold compactActiveWorklist
    rw [List.map_filterMap]
    apply nodup_filterMap_inj _ (List.range numJobs) List.nodup_range
    intro j₁ hj₁ j₂ hj₂ slot h₁ h₂
    rw [List.mem_range] at hj₁ hj₂
    split at h₁
    · split at h₁
      · simp only [Option.map_some, Option.some.injEq] at h₁
        split at h₂
        · split at h₂
          · simp only [Option.map_some, Option.some.injEq] at h₂
            exact hs.injective j₁ j₂ hj₁ hj₂ (h₁.trans h₂.symm)
          · cases h₂
        · cases h₂
      · cases h₁
    · cases h₁
  · intro j hj hb hrun
    unfold compactActiveWorklist
    rw [List.mem_map]
    refine ⟨⟨j, slotOf j⟩, List.mem_filterMap.mpr ?_, rfl⟩
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    simp [hb, hrun]

/-- Execute one quantum of `q` steps on a single active worklist entry in place,
    leaving all other `scr`/stack slots untouched. -/
def stepWorkEntry (q : Nat) (slots : Array MachineState) (w : WorkEntry) :
    Array MachineState :=
  if h : w.stateSlot < slots.size then
    slots.set w.stateSlot (runQuantum q slots[w.stateSlot]) h
  else
    slots

/-- Execute one GPU quantum across a compacted active worklist. -/
def dispatchQuantum (q : Nat) (slots : Array MachineState)
    (wl : List WorkEntry) : Array MachineState :=
  wl.foldl (stepWorkEntry q) slots

private theorem dispatchQuantum_size (q : Nat) :
    ∀ (wl : List WorkEntry) (slots : Array MachineState),
      (dispatchQuantum q slots wl).size = slots.size
  | [], _ => rfl
  | w :: wl, slots => by
    unfold dispatchQuantum
    rw [List.foldl_cons]
    have hstep : (stepWorkEntry q slots w).size = slots.size := by
      unfold stepWorkEntry
      split
      · rw [Array.size_set]
      · rfl
    exact (dispatchQuantum_size q wl (stepWorkEntry q slots w)).trans hstep

private theorem dispatchQuantum_cons (q : Nat) (slots : Array MachineState)
    (w : WorkEntry) (wl : List WorkEntry) :
    dispatchQuantum q slots (w :: wl) = dispatchQuantum q (stepWorkEntry q slots w) wl :=
  List.foldl_cons

private theorem dispatchQuantum_getElem (q : Nat) :
    ∀ (wl : List WorkEntry) (slots : Array MachineState) (i : Nat) (hi : i < slots.size),
      (wl.map WorkEntry.stateSlot).Nodup ->
      (∀ w ∈ wl, w.stateSlot < slots.size) ->
      (dispatchQuantum q slots wl)[i]'(by rw [dispatchQuantum_size]; exact hi) =
        if i ∈ wl.map WorkEntry.stateSlot then runQuantum q slots[i] else slots[i]
  | [], slots, i, hi, _, _ => by
    simp [dispatchQuantum]
  | w :: wl, slots, i, hi, hnd, hbounds => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hw : w.stateSlot < slots.size := hbounds w (List.mem_cons_self ..)
    have hsz1 : (stepWorkEntry q slots w).size = slots.size := by
      unfold stepWorkEntry
      simp [hw, Array.size_set]
    have hbounds' : ∀ w' ∈ wl, w'.stateSlot < (stepWorkEntry q slots w).size := by
      intro w' hw'
      rw [hsz1]
      exact hbounds w' (List.mem_cons_of_mem w hw')
    have ih := dispatchQuantum_getElem q wl (stepWorkEntry q slots w) i
      (by rw [hsz1]; exact hi) hnd.2 hbounds'
    simp only [dispatchQuantum_cons]
    rw [ih]
    by_cases heq : i = w.stateSlot
    · subst heq
      have hnot : w.stateSlot ∉ wl.map WorkEntry.stateSlot := hnd.1
      have hmem : w.stateSlot ∈ w.stateSlot :: wl.map WorkEntry.stateSlot := List.mem_cons_self ..
      simp only [List.map_cons, hnot, ↓reduceIte, hmem]
      have hself : (stepWorkEntry q slots w)[w.stateSlot]'(by rw [hsz1]; exact hw) =
          runQuantum q slots[w.stateSlot] := by
        unfold stepWorkEntry
        simp [hw, Array.getElem_set_self]
      rw [hself]
    · have hne : w.stateSlot ≠ i := Ne.symm heq
      have hset : (stepWorkEntry q slots w)[i]'(by rw [hsz1]; exact hi) = slots[i] := by
        unfold stepWorkEntry
        simp [hw, Array.getElem_set_ne hw hi hne]
      have hmem_iff :
          i ∈ w.stateSlot :: wl.map WorkEntry.stateSlot ↔ i ∈ wl.map WorkEntry.stateSlot := by
        simp [List.mem_cons, heq]
      simp only [List.map_cons, hset, hmem_iff]

/-- Execute `k` sequential compacted quanta starting from quantum index `stepIdx`. -/
def runCompactedFrom (q : Nat)
    (hostCompact : Nat -> Array MachineState -> List WorkEntry) :
    Nat -> Nat -> Array MachineState -> Array MachineState
  | _, 0, slots => slots
  | stepIdx, k + 1, slots =>
    runCompactedFrom q hostCompact (stepIdx + 1) k
      (dispatchQuantum q slots (hostCompact stepIdx slots))

/-- Execute `numQuanta` time-sliced quanta with host-driven retirement of finished
    lanes and injective slot compaction between quanta. -/
def runCompactedQuanta (q : Nat)
    (hostCompact : Nat -> Array MachineState -> List WorkEntry)
    (numQuanta : Nat) (initSlots : Array MachineState) : Array MachineState :=
  runCompactedFrom q hostCompact 0 numQuanta initSlots

private theorem runCompactedFrom_size (q : Nat)
    (hostCompact : Nat -> Array MachineState -> List WorkEntry) :
    ∀ (k stepIdx : Nat) (slots : Array MachineState),
      (runCompactedFrom q hostCompact stepIdx k slots).size = slots.size
  | 0, _, _ => rfl
  | k + 1, stepIdx, slots => by
    unfold runCompactedFrom
    rw [runCompactedFrom_size q hostCompact k (stepIdx + 1) _]
    exact dispatchQuantum_size q (hostCompact stepIdx slots) slots

theorem runCompactedQuanta_size (q : Nat)
    (hostCompact : Nat -> Array MachineState -> List WorkEntry)
    (numQuanta : Nat) (initSlots : Array MachineState) :
    (runCompactedQuanta q hostCompact numQuanta initSlots).size = initSlots.size :=
  runCompactedFrom_size q hostCompact numQuanta 0 initSlots

private theorem dispatchQuantum_slot_eq {numJobs q : Nat} {slotOf : Nat -> Nat}
    {slots : Array MachineState} {wl : List WorkEntry} {initSize : Nat}
    (hsz : slots.size = initSize)
    (hs : SlotMapWF numJobs slotOf initSize)
    (hwf : CompactedWorklistWF numJobs slotOf slots wl)
    {j : Nat} (hj : j < numJobs) :
    (dispatchQuantum q slots wl)[slotOf j]'(by
      rw [dispatchQuantum_size, hsz]; exact hs.inBounds j hj) =
      runMachine q (slots[slotOf j]'(by rw [hsz]; exact hs.inBounds j hj)) := by
  have hb : slotOf j < slots.size := by rw [hsz]; exact hs.inBounds j hj
  have hbounds : ∀ w ∈ wl, w.stateSlot < slots.size := by
    intro w hw
    obtain ⟨hwj, hws⟩ := hwf.entriesValid w hw
    rw [hws, hsz]
    exact hs.inBounds w.jobIdx hwj
  rw [dispatchQuantum_getElem q wl slots (slotOf j) hb hwf.slotsNodup hbounds]
  by_cases hmem : slotOf j ∈ wl.map WorkEntry.stateSlot
  · simp only [hmem, ↓reduceIte]
    exact runQuantum_eq_runMachine q (slots[slotOf j]'hb)
  · simp only [hmem, ↓reduceIte]
    have hnr : (slots[slotOf j]'hb).status ≠ .running := by
      intro hrun
      exact hmem (hwf.activeComplete j hj hb hrun)
    exact (runMachine_nonrunning q hnr).symm

private theorem compactedBatch_from_eq {numJobs q : Nat} {slotOf : Nat -> Nat}
    {hostCompact : Nat -> Array MachineState -> List WorkEntry}
    (initSize : Nat)
    (hs : SlotMapWF numJobs slotOf initSize)
    (hwf : ∀ stepIdx slots, slots.size = initSize ->
      CompactedWorklistWF numJobs slotOf slots (hostCompact stepIdx slots)) :
    ∀ (k stepIdx : Nat) (slots : Array MachineState) (hsz : slots.size = initSize)
      (j : Nat) (hj : j < numJobs),
      (runCompactedFrom q hostCompact stepIdx k slots)[slotOf j]'(by
        rw [runCompactedFrom_size, hsz]; exact hs.inBounds j hj) =
        runMachine (k * q) (slots[slotOf j]'(by rw [hsz]; exact hs.inBounds j hj))
  | 0, _, _, _, _, _ => by simp [runCompactedFrom, runMachine]
  | k + 1, stepIdx, slots, hsz, j, hj => by
    simp only [runCompactedFrom]
    let wl := hostCompact stepIdx slots
    let slots' := dispatchQuantum q slots wl
    have hsz' : slots'.size = initSize := by
      unfold slots'
      rw [dispatchQuantum_size, hsz]
    have ih := compactedBatch_from_eq (q := q) initSize hs hwf k (stepIdx + 1) slots' hsz' j hj
    have hstep := dispatchQuantum_slot_eq (q := q) hsz hs (hwf stepIdx slots hsz) hj
    rw [ih]
    change runMachine (k * q) (slots'[slotOf j]'_) = _
    rw [hstep, ← runMachine_add q (k * q) _, Nat.succ_mul, Nat.add_comm]

/-- Per-slot equivalence between `K` compacted quanta of `q` steps and
    uncompacted sequential execution of `K * q` steps, with backing state slots
    stationary (`scr`/stack slices never copied or moved). -/
theorem compactedBatch_eq_runMachine {numJobs K q : Nat} {slotOf : Nat -> Nat}
    {hostCompact : Nat -> Array MachineState -> List WorkEntry}
    {initSlots : Array MachineState}
    (hs : SlotMapWF numJobs slotOf initSlots.size)
    (hwf : ∀ stepIdx slots, slots.size = initSlots.size ->
      CompactedWorklistWF numJobs slotOf slots (hostCompact stepIdx slots))
    {j : Nat} (hj : j < numJobs) :
    (runCompactedQuanta q hostCompact K initSlots)[slotOf j]'(by
      rw [runCompactedQuanta_size]; exact hs.inBounds j hj) =
      runMachine (K * q) (initSlots[slotOf j]'(hs.inBounds j hj)) :=
  compactedBatch_from_eq initSlots.size hs hwf K 0 initSlots rfl j hj

/-- End-to-end soundness of time-sliced multi-quantum execution with host-side
    lane retirement and injective active-worklist compaction:
    preserves `runSteps (K * q)` verdicts, `delegate_never_accepts` monotonicity
    across all intermediate quanta `m ≤ K`, and `stepMachine_hasType` typing soundness. -/
theorem compactedBatch_sound {numJobs K q : Nat} {slotOf : Nat -> Nat}
    {hostCompact : Nat -> Array MachineState -> List WorkEntry}
    {initSlots : Array MachineState}
    (hs : SlotMapWF numJobs slotOf initSlots.size)
    (hwf : ∀ stepIdx slots, slots.size = initSlots.size ->
      CompactedWorklistWF numJobs slotOf slots (hostCompact stepIdx slots))
    {j : Nat} (hj : j < numJobs) :
    let hb0 : slotOf j < initSlots.size := hs.inBounds j hj
    let finalSlots := runCompactedQuanta q hostCompact K initSlots
    let hbF : slotOf j < finalSlots.size := by
      rw [runCompactedQuanta_size]; exact hb0
    let s0 := initSlots[slotOf j]'hb0
    let sf := finalSlots[slotOf j]'hbF
    sf = runMachine (K * q) s0 ∧
    sf.status = runSteps (K * q) s0 ∧
    (∀ r m, m ≤ K ->
      let midSlots := runCompactedQuanta q hostCompact m initSlots
      let hbM : slotOf j < midSlots.size := by rw [runCompactedQuanta_size]; exact hb0
      (midSlots[slotOf j]'hbM).status = .delegate r ->
      ∀ ty, sf.status = .delegate r ∧ sf.status ≠ .ok ty) ∧
    (∀ {cfg : MachineLimits} {gpuEnv : Array GpuConstDecl} {pers : SoATier}
        {env : KEnv} {ej : EIdx} {kej : KExpr} {ty : EIdx},
      s0 = initInfer cfg gpuEnv pers ej ->
      EnvSound pers gpuEnv env ->
      Interprets pers .empty ej kej ->
      sf.status = .ok ty ->
      ∃ kty, Interprets pers sf.scr ty kty ∧ HasType env [] kej kty) := by
  intro hb0 finalSlots hbF s0 sf
  have hfeq : sf = runMachine (K * q) s0 := compactedBatch_eq_runMachine hs hwf hj
  refine ⟨hfeq, ?_, ?_, ?_⟩
  · simp [runSteps, hfeq]
  · intro r m hm midSlots hbM hdel ty
    have hmeq : midSlots[slotOf j]'hbM = runMachine (m * q) s0 :=
      compactedBatch_eq_runMachine hs hwf hj
    have hdm : (runMachine (m * q) s0).status = .delegate r := by
      rw [← hmeq]
      exact hdel
    have hmon := runSteps_delegate_monotonic (ty := ty) (Nat.mul_le_mul_right q hm) hdm
    simpa [runSteps, hfeq] using hmon
  · intro cfg gpuEnv pers env ej kej ty hinit henv he hok
    have hok' : runSteps (K * q) (initInfer cfg gpuEnv pers ej) = .ok ty := by
      unfold runSteps
      rw [← hinit, ← hfeq]
      exact hok
    obtain ⟨kty, hty, hhas⟩ := stepMachine_hasType henv he hok'
    exact ⟨kty, by simpa [hfeq, hinit] using hty, hhas⟩

/-! ### 8. Epoch-Tagged Per-Lane Memoization Soundness (`epochMemo_hit_sound`) -/

private theorem stepEvalInfer_scr_extends {s : MachineState} {ctx : List EIdx} {e : EIdx} :
    TierExtends s.scr (stepEvalInfer s ctx e).scr := by
  unfold stepEvalInfer
  cases Arena.lookupNode s.pers s.scr e with
  | none => exact tierExtends_refl _
  | some c =>
    cases c with
    | bvar _ => exact tierExtends_refl _
    | fvar id => dsimp only; cases ctx[id.toNat]? <;> exact tierExtends_refl _
    | sort lvl =>
      dsimp only
      split
      · cases ha : allocScr s.cfg s.scr (.sort (UInt32.ofNat (lvl.toNat + 1))) with
        | ok scr₁ res => exact allocScr_extends ha
        | err _ | delegate _ => exact tierExtends_refl _
      · exact tierExtends_refl _
    | const cid => dsimp only; cases s.gpuEnv[cid.toNat]? <;> exact tierExtends_refl _
    | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ =>
      dsimp only; unfold pushFrame; split <;> exact tierExtends_refl _

private theorem stepEvalWhnf_scr_extends {s : MachineState} {e : EIdx}
    (wf : ScratchColsWF s.scr) :
    TierExtends s.scr (stepEvalWhnf s e).scr := by
  unfold stepEvalWhnf
  cases Arena.lookupNode s.pers s.scr e with
  | none => exact tierExtends_refl _
  | some c =>
    cases c with
    | bvar _ | fvar _ | sort _ | lam _ _ | forallE _ _ => exact tierExtends_refl _
    | const cid =>
      dsimp only
      cases s.gpuEnv[cid.toNat]? with
      | none => exact tierExtends_refl _
      | some decl => dsimp only; cases decl.val? <;> exact tierExtends_refl _
    | letE _ val body =>
      dsimp only
      cases hi : scratchInst s.cfg s.pers s.scr s.cfg.maxSteps 0 val body with
      | ok scr₁ res => exact (scratchInst_extends s.cfg s.pers s.cfg.maxSteps s.scr scr₁ 0 val body res wf hi).2
      | err _ | delegate _ => exact tierExtends_refl _
    | app _ _ =>
      dsimp only; unfold pushFrame; split <;> exact tierExtends_refl _

private theorem stepEvalDefEq_scr_extends {s : MachineState} {fid : Nat} {a b : EIdx} :
    TierExtends s.scr (stepEvalDefEq s fid a b).scr := by
  unfold stepEvalDefEq
  split
  · exact tierExtends_refl _
  · unfold pushFrame; split <;> exact tierExtends_refl _

private theorem stepDefEqRhsCells_scr_extends {s : MachineState} {fid : Nat}
    {rest : KontStack} {c₁ c₂ : ExprCell} (wf : ScratchColsWF s.scr) :
    TierExtends s.scr (stepDefEqRhsCells s fid rest c₁ c₂).scr := by
  cases c₁ <;> cases c₂ <;> simp only [stepDefEqRhsCells]
  all_goals try exact tierExtends_refl _
  · split
    · cases h1 : allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
      | err _ | delegate _ => dsimp only; exact tierExtends_refl _
      | ok scr₁ fv =>
        dsimp only
        have wf₁ := (allocScr_wf s.pers wf h1).1
        have ex₁ := allocScr_extends h1
        cases h2 : scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv _ with
        | err _ | delegate _ => dsimp only; exact tierExtends_refl _
        | ok scr₂ b₁' =>
          dsimp only
          have h2e := scratchInst_extends s.cfg s.pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ b₁' wf₁ h2
          cases h3 : scratchInst s.cfg s.pers scr₂ s.cfg.maxSteps 0 fv _ with
          | err _ | delegate _ => dsimp only; exact tierExtends_refl _
          | ok scr₃ b₂' =>
            dsimp only
            have h3e := scratchInst_extends s.cfg s.pers s.cfg.maxSteps scr₂ scr₃ 0 fv _ b₂' h2e.1 h3
            exact tierExtends_trans ex₁ (tierExtends_trans h2e.2 h3e.2)
    · exact tierExtends_refl _
  · split
    · cases h1 : allocScr s.cfg s.scr (.fvar (UInt32.ofNat fid)) with
      | err _ | delegate _ => dsimp only; exact tierExtends_refl _
      | ok scr₁ fv =>
        dsimp only
        have wf₁ := (allocScr_wf s.pers wf h1).1
        have ex₁ := allocScr_extends h1
        cases h2 : scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv _ with
        | err _ | delegate _ => dsimp only; exact tierExtends_refl _
        | ok scr₂ b₁' =>
          dsimp only
          have h2e := scratchInst_extends s.cfg s.pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ b₁' wf₁ h2
          cases h3 : scratchInst s.cfg s.pers scr₂ s.cfg.maxSteps 0 fv _ with
          | err _ | delegate _ => dsimp only; exact tierExtends_refl _
          | ok scr₃ b₂' =>
            dsimp only
            have h3e := scratchInst_extends s.cfg s.pers s.cfg.maxSteps scr₂ scr₃ 0 fv _ b₂' h2e.1 h3
            exact tierExtends_trans ex₁ (tierExtends_trans h2e.2 h3e.2)
    · exact tierExtends_refl _

private theorem stepRetInfer_scr_extends {s : MachineState} {f : Frame} {rest : KontStack}
    {ty : EIdx} (wf : ScratchColsWF s.scr) :
    TierExtends s.scr (stepRetInfer s f rest ty).scr := by
  cases f <;> simp only [stepRetInfer]
  all_goals try exact tierExtends_refl _
  · cases h1 : scratchAbst s.cfg s.pers s.scr s.cfg.maxSteps 0 _ ty with
    | err _ | delegate _ => dsimp only; exact tierExtends_refl _
    | ok scr₁ tyAbs =>
      dsimp only
      have h1e := scratchAbst_extends s.cfg s.pers s.cfg.maxSteps s.scr scr₁ 0 _ ty tyAbs wf h1
      cases h2 : allocScr s.cfg scr₁ (.forallE _ tyAbs) with
      | err _ | delegate _ => dsimp only; exact tierExtends_refl _
      | ok scr₂ res => exact tierExtends_trans h1e.2 (allocScr_extends h2)
  · cases h1 : scratchAbst s.cfg s.pers s.scr s.cfg.maxSteps 0 _ ty with
    | err _ | delegate _ => dsimp only; exact tierExtends_refl _
    | ok scr₁ tyAbs =>
      dsimp only
      have h1e := scratchAbst_extends s.cfg s.pers s.cfg.maxSteps s.scr scr₁ 0 _ ty tyAbs wf h1
      cases h2 : allocScr s.cfg scr₁ (.letE _ _ tyAbs) with
      | err _ | delegate _ => dsimp only; exact tierExtends_refl _
      | ok scr₂ res => exact tierExtends_trans h1e.2 (allocScr_extends h2)

private theorem stepRetWhnf_scr_extends {s : MachineState} {f : Frame} {rest : KontStack}
    {w : EIdx} (wf : ScratchColsWF s.scr) :
    TierExtends s.scr (stepRetWhnf s f rest w).scr := by
  cases f <;> simp only [stepRetWhnf]
  all_goals try exact tierExtends_refl _
  · cases Arena.lookupNode s.pers s.scr w with
    | none => exact tierExtends_refl _
    | some c => cases c <;> exact tierExtends_refl _
  · cases Arena.lookupNode s.pers s.scr w with
    | none => exact tierExtends_refl _
    | some c =>
      cases c with
      | sort _ =>
        dsimp only
        split
        · cases h1 : allocScr s.cfg s.scr (.fvar _) with
          | err _ | delegate _ => dsimp only; exact tierExtends_refl _
          | ok scr₁ fv =>
            dsimp only
            have wf₁ := (allocScr_wf s.pers wf h1).1
            have ex₁ := allocScr_extends h1
            cases h2 : scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv _ with
            | err _ | delegate _ => dsimp only; exact tierExtends_refl _
            | ok scr₂ body' =>
              dsimp only
              have h2e := scratchInst_extends s.cfg s.pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ body' wf₁ h2
              exact tierExtends_trans ex₁ h2e.2
        · exact tierExtends_refl _
      | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ =>
        exact tierExtends_refl _
  · cases Arena.lookupNode s.pers s.scr w with
    | none => exact tierExtends_refl _
    | some c =>
      cases c with
      | sort _ =>
        dsimp only
        split
        · cases h1 : allocScr s.cfg s.scr (.fvar _) with
          | err _ | delegate _ => dsimp only; exact tierExtends_refl _
          | ok scr₁ fv =>
            dsimp only
            have wf₁ := (allocScr_wf s.pers wf h1).1
            have ex₁ := allocScr_extends h1
            cases h2 : scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv _ with
            | err _ | delegate _ => dsimp only; exact tierExtends_refl _
            | ok scr₂ body' =>
              dsimp only
              have h2e := scratchInst_extends s.cfg s.pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ body' wf₁ h2
              exact tierExtends_trans ex₁ h2e.2
        · exact tierExtends_refl _
      | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ =>
        exact tierExtends_refl _
  · cases Arena.lookupNode s.pers s.scr w with
    | none => exact tierExtends_refl _
    | some c =>
      cases c with
      | sort v =>
        dsimp only
        cases h1 : allocScr s.cfg s.scr (.sort _) with
        | err _ | delegate _ => exact tierExtends_refl _
        | ok scr₁ _ => exact allocScr_extends h1
      | bvar _ | fvar _ | const _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ =>
        exact tierExtends_refl _
  · cases Arena.lookupNode s.pers s.scr w with
    | none => exact tierExtends_refl _
    | some c => cases c <;> exact tierExtends_refl _
  · cases Arena.lookupNode s.pers s.scr w with
    | none => exact tierExtends_refl _
    | some c =>
      cases c with
      | lam _ body =>
        dsimp only
        cases h1 : scratchInst s.cfg s.pers s.scr s.cfg.maxSteps 0 _ body with
        | err _ | delegate _ => exact tierExtends_refl _
        | ok scr₁ res =>
          exact (scratchInst_extends s.cfg s.pers s.cfg.maxSteps s.scr scr₁ 0 _ body res wf h1).2
      | bvar _ | fvar _ | sort _ | const _ | app _ _ | forallE _ _ | letE _ _ _ =>
        dsimp only
        cases h1 : allocScr s.cfg s.scr (.app w _) with
        | err _ | delegate _ => exact tierExtends_refl _
        | ok scr₁ _ => exact allocScr_extends h1
  · cases Arena.lookupNode s.pers s.scr _ with
    | none => exact tierExtends_refl _
    | some c₁ =>
      cases Arena.lookupNode s.pers s.scr w with
      | none => exact tierExtends_refl _
      | some c₂ => exact stepDefEqRhsCells_scr_extends wf

private theorem stepRetDefEq_scr_extends {s : MachineState} {f : Frame} {rest : KontStack}
    {ok : Bool} (wf : ScratchColsWF s.scr) :
    TierExtends s.scr (stepRetDefEq s f rest ok).scr := by
  cases f <;> simp only [stepRetDefEq]
  all_goals try exact tierExtends_refl _
  · split
    · cases h1 : scratchInst s.cfg s.pers s.scr s.cfg.maxSteps 0 _ _ with
      | err _ | delegate _ => exact tierExtends_refl _
      | ok scr₁ res => exact (scratchInst_extends s.cfg s.pers s.cfg.maxSteps s.scr scr₁ 0 _ _ res wf h1).2
    · exact tierExtends_refl _
  · split
    · split
      · cases h1 : allocScr s.cfg s.scr (.fvar _) with
        | err _ | delegate _ => dsimp only; exact tierExtends_refl _
        | ok scr₁ fv =>
          dsimp only
          have wf₁ := (allocScr_wf s.pers wf h1).1
          have ex₁ := allocScr_extends h1
          cases h2 : scratchInst s.cfg s.pers scr₁ s.cfg.maxSteps 0 fv _ with
          | err _ | delegate _ => dsimp only; exact tierExtends_refl _
          | ok scr₂ res =>
            exact tierExtends_trans ex₁
              (scratchInst_extends s.cfg s.pers s.cfg.maxSteps scr₁ scr₂ 0 fv _ res wf₁ h2).2
      · exact tierExtends_refl _
    · exact tierExtends_refl _
  · split <;> exact tierExtends_refl _

theorem step_scr_extends {s : MachineState} (wf : ScratchColsWF s.scr) :
    TierExtends s.scr (step s).scr := by
  unfold step
  split
  · exact tierExtends_refl _
  · split
    · exact tierExtends_refl _
    · cases hc : s.ctrl with
      | evalInfer ctx e => exact stepEvalInfer_scr_extends
      | evalWhnf e => exact stepEvalWhnf_scr_extends wf
      | evalDefEq fid a b => exact stepEvalDefEq_scr_extends
      | retInfer ty =>
        cases hst : s.stack with
        | nil => exact tierExtends_refl _
        | cons f rest => exact stepRetInfer_scr_extends wf
      | retWhnf w =>
        cases hst : s.stack with
        | nil => exact tierExtends_refl _
        | cons f rest => exact stepRetWhnf_scr_extends wf
      | retDefEq ok =>
        cases hst : s.stack with
        | nil => exact tierExtends_refl _
        | cons f rest => exact stepRetDefEq_scr_extends wf

/-- Keys cached by epoch-tagged per-lane scratch memoization (`typecheck_arena.wgsl`). -/
inductive MemoKey where
  | whnf (e : EIdx)
  | infer (e : EIdx)
  | defEq (fid : Nat) (a b : EIdx)
  deriving DecidableEq, Repr, Inhabited

/-- Values cached in epoch-tagged per-lane memoization slots. -/
inductive MemoVal where
  | whnf (w : EIdx)
  | infer (ty : EIdx)
  | defEq (ok : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Single epoch-stamped memo slot; entries with `epoch ≠ curEpoch` are stale and skipped
    on lookup without requiring an O(N) zeroing loop on each new job. -/
structure MemoEntry where
  epoch : Nat
  key : MemoKey
  val : MemoVal
  deriving DecidableEq, Repr, Inhabited

abbrev MemoTable := Array (Option MemoEntry)

/-- GPU state machine paired with current job epoch and epoch-tagged memo table. -/
structure MemoMachineState where
  core : MachineState
  epoch : Nat
  memo : MemoTable
  slotOf : MemoKey -> Nat

/-- Epoch-guarded memo lookup: rejects any entry whose epoch differs from `curEpoch`
    or whose stored key differs from `key`. -/
def memoLookup (curEpoch : Nat) (memo : MemoTable) (slotOf : MemoKey -> Nat)
    (key : MemoKey) : Option MemoVal :=
  match memo[slotOf key]? with
  | some (some entry) =>
    if entry.epoch == curEpoch && entry.key == key then some entry.val else none
  | _ => none

/-- Epoch-guarded memo insertion into `slotOf key`. -/
def memoInsert (curEpoch : Nat) (memo : MemoTable) (slotOf : MemoKey -> Nat)
    (key : MemoKey) (val : MemoVal) : MemoTable :=
  let slot := slotOf key
  if h : slot < memo.size then
    memo.set slot (some { epoch := curEpoch, key := key, val := val })
  else
    memo

/-- Advance to the next job epoch and reset scratch to `.empty` without clearing `memo`. -/
def advanceEpoch (ms : MemoMachineState) (nextCtrl : Control) : MemoMachineState :=
  { ms with
    core := { ms.core with
      scr := SoATier.empty
      ctrl := nextCtrl
      stack := []
      stepsUsed := 0
      status := .running }
    epoch := ms.epoch + 1 }

/-- Semantic validity of a cached `(key, val)` pair relative to `(env, pers, scr)`. -/
def MemoEntryValid (env : KEnv) (pers scr : SoATier) : MemoKey -> MemoVal -> Prop
  | .whnf e, .whnf w =>
    ∃ ke kw f, Interprets pers scr e ke ∧ Interprets pers scr w kw ∧ whnfFuel env f ke = some kw
  | .infer e, .infer ty =>
    ∃ ke kty f, Interprets pers scr e ke ∧ Interprets pers scr ty kty ∧ inferSpec env f [] ke = some kty
  | .defEq fid a b, .defEq ok =>
    ∃ ka kb, Interprets pers scr a ka ∧ Interprets pers scr b kb ∧
      (ok = true -> ∃ f, defEqSpec env f fid ka kb = true)
  | _, _ => False

/-- Memo table invariant at `(env, pers, scr, curEpoch)`:
    all present slots have `entry.epoch ≤ curEpoch`, and every slot stamped with
    `curEpoch` stores a semantically valid `(key, val)` pair. Stale entries with
    `entry.epoch < curEpoch` impose zero obligations on `scr`. -/
def MemoTableInv (env : KEnv) (pers scr : SoATier) (curEpoch : Nat) (memo : MemoTable) : Prop :=
  ∀ (slot : Nat) (entry : MemoEntry), memo[slot]? = some (some entry) ->
    entry.epoch ≤ curEpoch ∧
    (entry.epoch = curEpoch -> MemoEntryValid env pers scr entry.key entry.val)

theorem memoLookup_stale_none {curEpoch : Nat} {memo : MemoTable} {slotOf : MemoKey -> Nat}
    {key : MemoKey} {entry : MemoEntry}
    (hslot : memo[slotOf key]? = some (some entry)) (hne : entry.epoch ≠ curEpoch) :
    memoLookup curEpoch memo slotOf key = none := by
  unfold memoLookup
  rw [hslot]
  have hbeq : (entry.epoch == curEpoch) = false := beq_false_of_ne hne
  simp [hbeq]

theorem memoLookup_sound {env : KEnv} {pers scr : SoATier} {curEpoch : Nat}
    {memo : MemoTable} {slotOf : MemoKey -> Nat} {key : MemoKey} {val : MemoVal}
    (hinv : MemoTableInv env pers scr curEpoch memo)
    (hl : memoLookup curEpoch memo slotOf key = some val) :
    MemoEntryValid env pers scr key val := by
  unfold MemoTableInv at hinv
  unfold memoLookup at hl
  cases hs : memo[slotOf key]? with
  | none => rw [hs] at hl; cases hl
  | some m =>
    rw [hs] at hl
    cases m with
    | none => simp at hl
    | some entry =>
      dsimp only at hl
      split at hl
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at hl
        rw [← hc.2, ← hl]
        exact (hinv (slotOf key) entry hs).2 hc.1
      · cases hl

theorem memoInsert_preserves_inv {env : KEnv} {pers scr : SoATier} {curEpoch : Nat}
    {memo : MemoTable} {slotOf : MemoKey -> Nat} {key : MemoKey} {val : MemoVal}
    (hinv : MemoTableInv env pers scr curEpoch memo)
    (hval : MemoEntryValid env pers scr key val) :
    MemoTableInv env pers scr curEpoch (memoInsert curEpoch memo slotOf key val) := by
  unfold memoInsert
  by_cases hs : slotOf key < memo.size
  · simp only [hs, ↓reduceDIte]
    unfold MemoTableInv at hinv ⊢
    intro slot entry hlu
    by_cases heq : slot = slotOf key
    · subst heq
      have hsz : slotOf key < (memo.set (slotOf key) (some { epoch := curEpoch, key := key, val := val })).size := by
        rw [Array.size_set]; exact hs
      rw [Array.getElem?_eq_getElem hsz, Array.getElem_set_self, Option.some.injEq, Option.some.injEq] at hlu
      subst hlu
      exact ⟨Nat.le_refl _, fun _ => hval⟩
    · have hget : (memo.set (slotOf key) (some { epoch := curEpoch, key := key, val := val }))[slot]? =
          memo[slot]? := by
        by_cases hlt : slot < memo.size
        · have hsz : slot < (memo.set (slotOf key) (some { epoch := curEpoch, key := key, val := val })).size := by
            rw [Array.size_set]; exact hlt
          rw [Array.getElem?_eq_getElem hsz, Array.getElem?_eq_getElem hlt,
            Array.getElem_set_ne hs hlt (Ne.symm heq)]
        · have hsz : (memo.set (slotOf key) (some { epoch := curEpoch, key := key, val := val })).size ≤ slot := by
            rw [Array.size_set]; exact Nat.le_of_not_lt hlt
          rw [Array.getElem?_eq_none hsz, Array.getElem?_eq_none (Nat.le_of_not_lt hlt)]
      rw [hget] at hlu
      exact hinv slot entry hlu
  · simp only [hs, ↓reduceDIte]
    exact hinv

theorem memoTableInv_extends {env : KEnv} {pers scr scr' : SoATier} {curEpoch : Nat}
    {memo : MemoTable} (hex : TierExtends scr scr')
    (hinv : MemoTableInv env pers scr curEpoch memo) :
    MemoTableInv env pers scr' curEpoch memo := by
  unfold MemoTableInv at hinv ⊢
  intro slot entry hlu
  obtain ⟨hle, hv⟩ := hinv slot entry hlu
  refine ⟨hle, fun heq => ?_⟩
  have hm := hv heq
  rcases entry with ⟨ep, ek, ev⟩
  dsimp only at hm ⊢
  cases ek <;> cases ev <;> simp only [MemoEntryValid] at hm ⊢
  all_goals try exact False.elim hm
  · rcases hm with ⟨ke, kw, f, he, hw, hwh⟩
    exact ⟨ke, kw, f, interprets_extends hex he, interprets_extends hex hw, hwh⟩
  · rcases hm with ⟨ke, kty, f, he, hty, hin⟩
    exact ⟨ke, kty, f, interprets_extends hex he, interprets_extends hex hty, hin⟩
  · rcases hm with ⟨ka, kb, ha, hb, hde⟩
    exact ⟨ka, kb, interprets_extends hex ha, interprets_extends hex hb, hde⟩

/-- Advancing `epoch := epoch + 1` with `scr := .empty` unconditionally preserves
    `MemoTableInv` without touching any existing slot in `memo`. -/
theorem advanceEpoch_preserves_memoInv {env : KEnv} {pers : SoATier}
    (ms : MemoMachineState) (nextCtrl : Control)
    (hinv : MemoTableInv env pers ms.core.scr ms.epoch ms.memo) :
    MemoTableInv env pers SoATier.empty (ms.epoch + 1) (advanceEpoch ms nextCtrl).memo := by
  unfold MemoTableInv at hinv ⊢
  intro slot entry hlu
  obtain ⟨hle, _⟩ := hinv slot entry hlu
  exact ⟨Nat.le_succ_of_le hle, fun h => by omega⟩

/-- Single step of the GPU machine accelerated by epoch-tagged memo hits. -/
def stepWithMemo (ms : MemoMachineState) : MemoMachineState :=
  let s := ms.core
  if s.status ≠ .running then
    ms
  else if s.cfg.maxSteps ≤ s.stepsUsed then
    { ms with core := { s with status := .delegate .stepExhausted } }
  else
    match s.ctrl with
    | .evalWhnf e =>
      match memoLookup ms.epoch ms.memo ms.slotOf (.whnf e) with
      | some (.whnf w) => { ms with core := goCtrl s s.scr (.retWhnf w) }
      | _ => { ms with core := step s }
    | .evalInfer [] e =>
      match memoLookup ms.epoch ms.memo ms.slotOf (.infer e) with
      | some (.infer ty) => { ms with core := goCtrl s s.scr (.retInfer ty) }
      | _ => { ms with core := step s }
    | .evalDefEq fid a b =>
      match memoLookup ms.epoch ms.memo ms.slotOf (.defEq fid a b) with
      | some (.defEq ok) => { ms with core := goCtrl s s.scr (.retDefEq ok) }
      | _ => { ms with core := step s }
    | _ => { ms with core := step s }

def runMachineMemo : Nat -> MemoMachineState -> MemoMachineState
  | 0, ms => ms
  | n + 1, ms => runMachineMemo n (stepWithMemo ms)

def runStepsMemo (n : Nat) (ms : MemoMachineState) : MachineStatus EIdx :=
  (runMachineMemo n ms).core.status

private theorem stepWithMemo_preserves_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr}
    {ms : MemoMachineState}
    (henv : EnvSound pers ms.core.gpuEnv env)
    (hs : StateOK env pers rootKE ms.core)
    (hinv : MemoTableInv env pers ms.core.scr ms.epoch ms.memo) :
    StateOK env pers rootKE (stepWithMemo ms).core ∧
    MemoTableInv env pers (stepWithMemo ms).core.scr (stepWithMemo ms).epoch (stepWithMemo ms).memo := by
  have wf : ScratchColsWF ms.core.scr := hs.2.1
  have hpers : ms.core.pers = pers := hs.1
  have stepCase :
      StateOK env pers rootKE (step ms.core) ∧
      MemoTableInv env pers (step ms.core).scr ms.epoch ms.memo := by
    refine ⟨step_preserves_ok henv hs, ?_⟩
    exact memoTableInv_extends (step_scr_extends wf) hinv
  unfold stepWithMemo
  dsimp only
  split
  · exact ⟨hs, hinv⟩
  · have hrunEq : ms.core.status = .running := by
      cases hst : ms.core.status <;> simp_all
    split
    · refine ⟨⟨hpers, wf, fun hr => by simp at hr, fun ty hok => by simp at hok⟩, hinv⟩
    · have hctrl := hs.2.2.1 hrunEq
      cases hct : ms.core.ctrl with
      | evalWhnf e =>
        cases hlu : memoLookup ms.epoch ms.memo ms.slotOf (.whnf e) with
        | none =>
          dsimp only; rw [hlu]
          exact stepCase
        | some mv =>
          cases mv with
          | whnf w =>
            dsimp only; rw [hlu]; dsimp only
            have hm := memoLookup_sound hinv hlu
            simp only [MemoEntryValid] at hm
            rcases hm with ⟨ke, kw, f, he, hw, hwh⟩
            rw [hct] at hctrl
            simp only [CtrlOK] at hctrl
            rcases hctrl with ⟨curKe, origKe, hcur, hwhOrig, hstack⟩
            have heq : curKe = ke := interprets_deterministic hcur he
            subst heq
            obtain ⟨f', hf'⟩ := hwhOrig kw f hwh
            refine ⟨⟨hpers, wf, ?_, ?_⟩, hinv⟩
            · intro _
              exact ⟨origKe, kw, hw, ⟨f', hf'⟩, hstack⟩
            · intro ty hok
              simp [goCtrl] at hok
          | infer _ | defEq _ =>
            dsimp only; rw [hlu]
            exact stepCase
      | evalInfer ctx e =>
        cases ctx with
        | nil =>
          cases hlu : memoLookup ms.epoch ms.memo ms.slotOf (.infer e) with
          | none =>
            dsimp only; rw [hlu]
            exact stepCase
          | some mv =>
            cases mv with
            | infer ty =>
              dsimp only; rw [hlu]; dsimp only
              have hm := memoLookup_sound hinv hlu
              simp only [MemoEntryValid] at hm
              rcases hm with ⟨ke, kty, f, he, hty, hin⟩
              rw [hct] at hctrl
              simp only [CtrlOK] at hctrl
              rcases hctrl with ⟨kctx, curKe, hkctx, hcur, hstack⟩
              have hnil : kctx = [] := List.eq_nil_of_length_eq_zero hkctx.1.symm
              subst hnil
              have heq : curKe = ke := interprets_deterministic hcur he
              subst heq
              refine ⟨⟨hpers, wf, ?_, ?_⟩, hinv⟩
              · intro _
                exact ⟨[], curKe, kty, hty, ⟨f, hin⟩, hstack⟩
              · intro ty' hok
                simp [goCtrl] at hok
            | whnf _ | defEq _ =>
              dsimp only; rw [hlu]
              exact stepCase
        | cons _ _ =>
          dsimp only
          exact stepCase
      | evalDefEq fid a b =>
        cases hlu : memoLookup ms.epoch ms.memo ms.slotOf (.defEq fid a b) with
        | none =>
          dsimp only; rw [hlu]
          exact stepCase
        | some mv =>
          cases mv with
          | defEq ok =>
            dsimp only; rw [hlu]; dsimp only
            have hm := memoLookup_sound hinv hlu
            simp only [MemoEntryValid] at hm
            rcases hm with ⟨ka', kb', ha', hb', hde'⟩
            rw [hct] at hctrl
            simp only [CtrlOK] at hctrl
            rcases hctrl with ⟨ka, kb, origFid, origKa, origKb, ha, hb, hdeOrig, hstack⟩
            have hka : ka = ka' := interprets_deterministic ha ha'
            have hkb : kb = kb' := interprets_deterministic hb hb'
            subst hka; subst hkb
            refine ⟨⟨hpers, wf, ?_, ?_⟩, hinv⟩
            · intro _
              exact ⟨origFid, origKa, origKb, fun hok => hdeOrig (hde' hok), hstack⟩
            · intro ty hok
              simp [goCtrl] at hok
          | whnf _ | infer _ =>
            dsimp only; rw [hlu]
            exact stepCase
      | retInfer _ | retWhnf _ | retDefEq _ =>
        dsimp only
        exact stepCase

private theorem stepWithMemo_preserves_gpuEnv (ms : MemoMachineState) :
    (stepWithMemo ms).core.gpuEnv = ms.core.gpuEnv := by
  unfold stepWithMemo
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · split <;> try exact step_preserves_gpuEnv ms.core
        rfl
      · split <;> try exact step_preserves_gpuEnv ms.core
        rfl
      · split <;> try exact step_preserves_gpuEnv ms.core
        rfl
      · exact step_preserves_gpuEnv ms.core

theorem runMachineMemo_preserves_ok {env : KEnv} {pers : SoATier} {rootKE : KExpr} :
    ∀ (n : Nat) (ms : MemoMachineState),
      EnvSound pers ms.core.gpuEnv env ->
      StateOK env pers rootKE ms.core ->
      MemoTableInv env pers ms.core.scr ms.epoch ms.memo ->
      StateOK env pers rootKE (runMachineMemo n ms).core ∧
      MemoTableInv env pers (runMachineMemo n ms).core.scr
        (runMachineMemo n ms).epoch (runMachineMemo n ms).memo
  | 0, ms, _, hs, hinv => ⟨hs, hinv⟩
  | n + 1, ms, henv, hs, hinv => by
    have ⟨hs', hinv'⟩ := stepWithMemo_preserves_ok henv hs hinv
    have henv' : EnvSound pers (stepWithMemo ms).core.gpuEnv env := by
      rw [stepWithMemo_preserves_gpuEnv ms]; exact henv
    exact runMachineMemo_preserves_ok n (stepWithMemo ms) henv' hs' hinv'

/-- **Theorem (`epochMemo_hit_sound`)**:
    Under the epoch-tagged memo table invariant (ignoring stale entries with `entry.epoch ≠ curEpoch`
    without per-job zeroing loops), every memo-accelerated GPU execution returning `.ok ty` is
    100% sound against both the functional specification `inferSpec` and the declarative typing
    judgment `HasType`. -/
theorem epochMemo_hit_sound {cfg : MachineLimits} {gpuEnv : Array GpuConstDecl}
    {pers : SoATier} {env : KEnv} {n epoch : Nat}
    {memo : MemoTable} {slotOf : MemoKey -> Nat}
    {e ty : EIdx} {ke : KExpr}
    (henv : EnvSound pers gpuEnv env)
    (he : Interprets pers .empty e ke)
    (hmemo : MemoTableInv env pers .empty epoch memo)
    (hok : runStepsMemo n
      { core := initInfer cfg gpuEnv pers e
        epoch := epoch
        memo := memo
        slotOf := slotOf } = .ok ty) :
    (∃ kty, Interprets pers (runMachineMemo n
      { core := initInfer cfg gpuEnv pers e
        epoch := epoch
        memo := memo
        slotOf := slotOf }).core.scr ty kty ∧
      ∃ fuel, inferSpec env fuel [] ke = some kty) ∧
    (∃ kty, Interprets pers (runMachineMemo n
      { core := initInfer cfg gpuEnv pers e
        epoch := epoch
        memo := memo
        slotOf := slotOf }).core.scr ty kty ∧
      HasType env [] ke kty) := by
  let ms0 : MemoMachineState :=
    { core := initInfer cfg gpuEnv pers e
      epoch := epoch
      memo := memo
      slotOf := slotOf }
  have hinit : StateOK env pers ke ms0.core := initInfer_stateOK he
  have ⟨hfin, _⟩ := runMachineMemo_preserves_ok n ms0 henv hinit hmemo
  obtain ⟨kty, hty, fuel, hspec⟩ := hfin.2.2.2 ty hok
  exact ⟨⟨kty, hty, fuel, hspec⟩, ⟨kty, hty, inferSpec_hasType env fuel [] ke kty hspec⟩⟩

end ConGpuProof
