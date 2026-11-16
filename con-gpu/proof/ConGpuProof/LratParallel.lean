/-
ConGpuProof.LratParallel
========================
Formal soundness proof for con-gpu's data-parallel GPU LRAT UNSAT verifier:
propositional CNF semantics, Reverse Unit Propagation (`checkRupStep`),
deletion-free strictly causal parallel LRAT verification (`verifyParallelLRAT`),
well-founded induction on derived clause index `i` (`derived_clause_entailed`),
and the top-level UNSAT soundness theorem `gpu_parallel_lrat_unsat`.
-/

namespace ConGpuProof

/-! ### 1. Propositional Literals, Clauses, CNF Formulas, and Semantics -/

/-- Signed propositional literal with 0-free unambiguous negation. -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr, Inhabited

def Lit.neg (l : Lit) : Lit :=
  ⟨l.var, !l.pos⟩

@[simp]
theorem Lit.neg_neg (l : Lit) : l.neg.neg = l := by
  cases l with
  | mk v p => cases p <;> rfl

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat -> Bool

def evalLit (a : Assignment) (l : Lit) : Bool :=
  if l.pos then a l.var else !(a l.var)

@[simp]
theorem evalLit_neg (a : Assignment) (l : Lit) :
    evalLit a l.neg = !(evalLit a l) := by
  cases l with
  | mk v p =>
    cases p <;> simp [Lit.neg, evalLit]

def evalClause (a : Assignment) (c : Clause) : Bool :=
  c.any (evalLit a)

@[simp]
theorem evalClause_nil (a : Assignment) : evalClause a [] = false := rfl

theorem evalClause_iff (a : Assignment) (c : Clause) :
    evalClause a c = true ↔ ∃ l ∈ c, evalLit a l = true := by
  simp [evalClause, List.any_eq_true]

theorem evalClause_false_iff (a : Assignment) (c : Clause) :
    evalClause a c = false ↔ ∀ l ∈ c, evalLit a l = false := by
  constructor
  · intro hf l hl
    cases hlt : evalLit a l with
    | false => rfl
    | true =>
      have hc : evalClause a c = true := (evalClause_iff a c).mpr ⟨l, hl, hlt⟩
      rw [hc] at hf
      cases hf
  · intro hforall
    cases hct : evalClause a c with
    | false => rfl
    | true =>
      rcases (evalClause_iff a c).mp hct with ⟨l, hl, hlt⟩
      have hlf := hforall l hl
      rw [hlt] at hlf
      cases hlf

def evalCNF (a : Assignment) (f : CNF) : Bool :=
  f.all (evalClause a)

theorem evalCNF_iff (a : Assignment) (f : CNF) :
    evalCNF a f = true ↔ ∀ c ∈ f, evalClause a c = true := by
  simp [evalCNF, List.all_eq_true]

def Satisfiable (f : CNF) : Prop :=
  ∃ a : Assignment, evalCNF a f = true

def Unsat (f : CNF) : Prop :=
  ¬ Satisfiable f

theorem unsat_iff_forall_false (f : CNF) :
    Unsat f ↔ ∀ a : Assignment, evalCNF a f = false := by
  constructor
  · intro hu a
    cases ht : evalCNF a f with
    | false => rfl
    | true => exact False.elim (hu ⟨a, ht⟩)
  · intro hforall ⟨a, ha⟩
    have hf := hforall a
    rw [ha] at hf
    cases hf

/-! ### 2. Reverse Unit Propagation (`checkRupStep`) & Soundness -/

inductive RupHintResult where
  | conflict
  | unit (u : Lit)
  | invalid
  deriving DecidableEq, Repr, Inhabited

private def hasLit (units : List Lit) (l : Lit) : Bool :=
  units.any (fun u => decide (u = l))

private theorem hasLit_iff_mem (units : List Lit) (l : Lit) :
    hasLit units l = true ↔ l ∈ units := by
  simp only [hasLit, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hl; exact ⟨l, hl, rfl⟩

/-- Classify a hint clause `h` against the currently forced true literals `units`
    (negation of the candidate derived clause plus earlier propagated units). -/
def evalHintUnder (units : List Lit) (h : Clause) : RupHintResult :=
  if h.any (fun x => hasLit units x) then
    .invalid
  else
    let rem := h.filter (fun x => !(hasLit units x.neg))
    match rem with
    | [] => .conflict
    | u :: rest =>
      if rest.all (fun x => decide (x = u)) then .unit u else .invalid

theorem evalHintUnder_conflict_false (a : Assignment) (units : List Lit) (h : Clause)
    (hunits : ∀ v ∈ units, evalLit a v = true)
    (hclause : evalClause a h = true)
    (hres : evalHintUnder units h = .conflict) :
    False := by
  unfold evalHintUnder at hres
  split at hres
  · cases hres
  · dsimp only at hres
    rcases (evalClause_iff a h).mp hclause with ⟨x, hxmem, hxa⟩
    cases hrem : h.filter (fun y => !(hasLit units y.neg)) with
    | cons u rest =>
      rw [hrem] at hres
      dsimp only at hres
      split at hres <;> cases hres
    | nil =>
      cases hneg : hasLit units x.neg with
      | true =>
        have hnegMem : x.neg ∈ units := (hasLit_iff_mem units x.neg).mp hneg
        have hnegT : evalLit a x.neg = true := hunits x.neg hnegMem
        rw [evalLit_neg, hxa] at hnegT
        cases hnegT
      | false =>
        have hxInRem : x ∈ h.filter (fun y => !(hasLit units y.neg)) := by
          rw [List.mem_filter]
          exact ⟨hxmem, by simp [hneg]⟩
        rw [hrem] at hxInRem
        cases hxInRem

theorem evalHintUnder_unit_true (a : Assignment) (units : List Lit) (h : Clause) (u : Lit)
    (hunits : ∀ v ∈ units, evalLit a v = true)
    (hclause : evalClause a h = true)
    (hres : evalHintUnder units h = .unit u) :
    evalLit a u = true := by
  unfold evalHintUnder at hres
  split at hres
  · cases hres
  · dsimp only at hres
    rcases (evalClause_iff a h).mp hclause with ⟨x, hxmem, hxa⟩
    cases hrem : h.filter (fun y => !(hasLit units y.neg)) with
    | nil => rw [hrem] at hres; cases hres
    | cons u₀ rest =>
      rw [hrem] at hres
      dsimp only at hres
      split at hres
      · next hall =>
        simp only [RupHintResult.unit.injEq] at hres
        cases hneg : hasLit units x.neg with
        | true =>
          have hnegMem : x.neg ∈ units := (hasLit_iff_mem units x.neg).mp hneg
          have hnegT : evalLit a x.neg = true := hunits x.neg hnegMem
          rw [evalLit_neg, hxa] at hnegT
          exact False.elim (Bool.noConfusion hnegT)
        | false =>
          have hxInRem : x ∈ h.filter (fun y => !(hasLit units y.neg)) := by
            rw [List.mem_filter]
            exact ⟨hxmem, by simp [hneg]⟩
          rw [hrem, List.mem_cons] at hxInRem
          rcases hxInRem with rfl | hxrest
          · rw [← hres]; exact hxa
          · have hall' : ∀ z ∈ rest, decide (z = u₀) = true := List.all_eq_true.mp hall
            have hxeq : x = u₀ := decide_eq_true_eq.mp (hall' x hxrest)
            rw [← hres, ← hxeq]
            exact hxa
      · cases hres

/-- Execute sequential unit propagation along a causal hint sequence. -/
def rupPropagate (lookupHint : Nat -> Option Clause) (units : List Lit) : List Nat -> Bool
  | [] => false
  | hid :: hs =>
    match lookupHint hid with
    | none => false
    | some hClause =>
      match evalHintUnder units hClause with
      | .conflict => true
      | .unit u => rupPropagate lookupHint (u :: units) hs
      | .invalid => false

/-- Check one RUP derivation step for clause `c` using `lookupHint` and `hints`. -/
def checkRupStep (lookupHint : Nat -> Option Clause) (c : Clause) (hints : List Nat) : Bool :=
  rupPropagate lookupHint (c.map Lit.neg) hints

theorem rupPropagate_sound (a : Assignment) (lookupHint : Nat -> Option Clause) :
    ∀ (hs : List Nat) (units : List Lit),
      (∀ v ∈ units, evalLit a v = true) ->
      (∀ hid ∈ hs, ∀ hClause, lookupHint hid = some hClause -> evalClause a hClause = true) ->
      rupPropagate lookupHint units hs = true ->
      False
  | [], _, _, _, h => by simp [rupPropagate] at h
  | hid :: hs, units, hunits, hhints, hrup => by
    simp only [rupPropagate] at hrup
    cases hlu : lookupHint hid with
    | none => rw [hlu] at hrup; cases hrup
    | some hClause =>
      rw [hlu] at hrup
      dsimp only at hrup
      have hClauseSat : evalClause a hClause = true :=
        hhints hid (List.mem_cons_self ..) hClause hlu
      cases hev : evalHintUnder units hClause with
      | invalid => rw [hev] at hrup; cases hrup
      | conflict =>
        exact evalHintUnder_conflict_false a units hClause hunits hClauseSat hev
      | unit u =>
        rw [hev] at hrup
        have hu : evalLit a u = true :=
          evalHintUnder_unit_true a units hClause u hunits hClauseSat hev
        have hunits' : ∀ v ∈ u :: units, evalLit a v = true := by
          intro v hv
          rw [List.mem_cons] at hv
          rcases hv with rfl | hvm
          · exact hu
          · exact hunits v hvm
        have hhints' : ∀ hid' ∈ hs, ∀ hc, lookupHint hid' = some hc -> evalClause a hc = true := by
          intro hid' hmem hc hlu'
          exact hhints hid' (List.mem_cons_of_mem hid hmem) hc hlu'
        exact rupPropagate_sound a lookupHint hs (u :: units) hunits' hhints' hrup

theorem checkRupStep_sound (a : Assignment) (lookupHint : Nat -> Option Clause)
    (c : Clause) (hints : List Nat)
    (hhints : ∀ hid ∈ hints, ∀ hClause, lookupHint hid = some hClause -> evalClause a hClause = true)
    (hrup : checkRupStep lookupHint c hints = true) :
    evalClause a c = true := by
  cases hct : evalClause a c with
  | true => rfl
  | false =>
    have hneg : ∀ v ∈ c.map Lit.neg, evalLit a v = true := by
      intro v hv
      rw [List.mem_map] at hv
      rcases hv with ⟨l, hl, rfl⟩
      have hlf := (evalClause_false_iff a c).mp hct l hl
      rw [evalLit_neg, hlf]
      rfl
    exact False.elim (rupPropagate_sound a lookupHint hints (c.map Lit.neg) hneg hhints hrup)

/-! ### 3. Data-Parallel GPU LRAT Verifier & Well-Founded Entailment Proof -/

/-- One derived LRAT proof step: target clause + hint clause indices. -/
structure LratStep where
  clause : Clause
  hints : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Deletion-free, strictly causal parallel clause lookup for derived step `i`:
    hints `hid < initCNF.length` resolve into `initCNF`; hints
    `initCNF.length ≤ hid < initCNF.length + i` resolve into `steps[j]` with
    `j < i`. Any `j ≥ i` or out-of-range hint returns `none` (rejected). -/
def lookupCausal (initCNF : CNF) (steps : Array LratStep) (i hid : Nat) : Option Clause :=
  if hid < initCNF.length then
    initCNF[hid]?
  else
    let j := hid - initCNF.length
    if j < i then
      if hsz : j < steps.size then some steps[j].clause else none
    else
      none

/-- Independent per-thread GPU check for derived step `i`. -/
def verifyStep (initCNF : CNF) (steps : Array LratStep) (i : Nat) (step : LratStep) : Bool :=
  checkRupStep (lookupCausal initCNF steps i) step.clause step.hints

/-- All derived steps `0 .. steps.size - 1` pass independently in parallel. -/
def verifyAllSteps (initCNF : CNF) (steps : Array LratStep) : Bool :=
  (List.range steps.size).all fun i =>
    if h : i < steps.size then verifyStep initCNF steps i steps[i] else false

/-- Parallel GPU LRAT verifier: every derived step checks independently and at
    least one verified step derives the empty clause `[]`. -/
def verifyParallelLRAT (initCNF : CNF) (steps : Array LratStep) : Bool :=
  verifyAllSteps initCNF steps &&
  (List.range steps.size).any fun i =>
    if h : i < steps.size then steps[i].clause.isEmpty else false

private theorem lookupCausal_sat (initCNF : CNF) (steps : Array LratStep)
    (a : Assignment) (ha : evalCNF a initCNF = true)
    (i : Nat)
    (hprev : ∀ j, j < i -> (hj : j < steps.size) -> evalClause a steps[j].clause = true) :
    ∀ hid hClause, lookupCausal initCNF steps i hid = some hClause ->
      evalClause a hClause = true := by
  intro hid hClause hlu
  unfold lookupCausal at hlu
  split at hlu
  · have hmem : hClause ∈ initCNF := List.mem_of_getElem? hlu
    exact (evalCNF_iff a initCNF).mp ha hClause hmem
  · dsimp only at hlu
    split at hlu
    · next hj =>
      split at hlu
      · next hltSize =>
        simp only [Option.some.injEq] at hlu
        rw [← hlu]
        exact hprev (hid - initCNF.length) hj hltSize
      · cases hlu
    · cases hlu

/-- Core logical entailment invariant proved by well-founded strong induction on
    clause index `i`: every derived clause `steps[i]` is logically entailed by
    `initCNF`. -/
theorem derived_clause_entailed (initCNF : CNF) (steps : Array LratStep)
    (hall : verifyAllSteps initCNF steps = true) :
    ∀ (i : Nat) (hi : i < steps.size) (a : Assignment),
      evalCNF a initCNF = true -> evalClause a steps[i].clause = true := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi a ha
    have hall' : ∀ k ∈ List.range steps.size,
        (if h : k < steps.size then verifyStep initCNF steps k steps[k] else false) = true :=
      List.all_eq_true.mp hall
    have hk := hall' i (List.mem_range.mpr hi)
    have hstepVer : verifyStep initCNF steps i steps[i] = true := by
      simpa [hi] using hk
    have hprev : ∀ j, j < i -> (hj : j < steps.size) ->
        evalClause a steps[j].clause = true := by
      intro j hjlt hj
      exact ih j hjlt hj a ha
    have hhints : ∀ hid ∈ steps[i].hints, ∀ hClause,
        lookupCausal initCNF steps i hid = some hClause ->
        evalClause a hClause = true := by
      intro hid _ hClause hlu
      exact lookupCausal_sat initCNF steps a ha i hprev hid hClause hlu
    exact checkRupStep_sound a (lookupCausal initCNF steps i) steps[i].clause steps[i].hints
      hhints hstepVer

/-- Main Theorem: if `verifyParallelLRAT initCNF steps = true`, then `initCNF` is
    mathematically unsatisfiable. -/
theorem gpu_parallel_lrat_unsat (initCNF : CNF) (steps : Array LratStep)
    (hver : verifyParallelLRAT initCNF steps = true) :
    Unsat initCNF := by
  unfold verifyParallelLRAT at hver
  rw [Bool.and_eq_true] at hver
  rcases hver with ⟨hall, hany⟩
  rw [List.any_eq_true] at hany
  rcases hany with ⟨k, hkRange, hkEmpty⟩
  have hkSize : k < steps.size := List.mem_range.mp hkRange
  have hkEmpty' : steps[k].clause.isEmpty = true := by
    simpa [hkSize] using hkEmpty
  have hkNil : steps[k].clause = [] := List.isEmpty_iff.mp hkEmpty'
  intro ⟨a, ha⟩
  have hsat := derived_clause_entailed initCNF steps hall k hkSize a ha
  rw [hkNil, evalClause_nil] at hsat
  cases hsat

/-! ### 4. Backward-Reachability LRAT Trimming Soundness (`TrimmedLratSubtrace`, `remapTrimmedSteps`, `trimLrat_sound`) -/

/-- Causal lookup restricted to original CNF clauses and strictly earlier *kept*
    derived steps (`j < i ∧ keep j = true`). Dead unkept clauses cannot be referenced. -/
def lookupKept (initCNF : CNF) (steps : Array LratStep) (keep : Nat -> Bool)
    (i hid : Nat) : Option Clause :=
  if hid < initCNF.length then
    initCNF[hid]?
  else
    let j := hid - initCNF.length
    if j < i && keep j then
      if _ : j < steps.size then some steps[j].clause else none
    else
      none

theorem lookupKept_sat (initCNF : CNF) (steps : Array LratStep) (keep : Nat -> Bool)
    (a : Assignment) (ha : evalCNF a initCNF = true) (i : Nat)
    (hprev : ∀ j, j < i -> (hj : j < steps.size) -> keep j = true ->
      evalClause a steps[j].clause = true)
    (hid : Nat) (hClause : Clause)
    (hlu : lookupKept initCNF steps keep i hid = some hClause) :
    evalClause a hClause = true := by
  unfold lookupKept at hlu
  split at hlu
  · exact (evalCNF_iff a initCNF).mp ha hClause (List.mem_of_getElem? hlu)
  · dsimp only at hlu
    split at hlu
    · next hjBoth =>
      simp only [Bool.and_eq_true] at hjBoth
      split at hlu
      · next hsz =>
        simp only [Option.some.injEq] at hlu
        rw [← hlu]
        exact hprev (hid - initCNF.length) (decide_eq_true_eq.mp hjBoth.1) hsz hjBoth.2
      · cases hlu
    · cases hlu

/-- Sparse backward-reachable sub-trace specification:
    1. Every kept step `i < origSteps.size` (`keep i = true`) passes RUP checking
       using only `initCNF` and strictly earlier *kept* steps `j < i`.
    2. At least one kept step derives the empty clause `[]`. -/
structure TrimmedLratSubtrace (initCNF : CNF) (origSteps : Array LratStep)
    (keep : Nat -> Bool) : Prop where
  stepsValid : ∀ (i : Nat) (hi : i < origSteps.size), keep i = true ->
    checkRupStep (lookupKept initCNF origSteps keep i)
      origSteps[i].clause origSteps[i].hints = true
  hasEmpty : ∃ (k : Nat) (hk : k < origSteps.size),
    keep k = true ∧ origSteps[k].clause.isEmpty = true

/-- Strong well-founded induction over kept step indices: every kept derived clause
    in a `TrimmedLratSubtrace` is logically entailed by `initCNF`. -/
theorem trimmedSubtrace_entailed (initCNF : CNF) (origSteps : Array LratStep)
    (keep : Nat -> Bool)
    (hvalid : ∀ (i : Nat) (hi : i < origSteps.size), keep i = true ->
      checkRupStep (lookupKept initCNF origSteps keep i)
        origSteps[i].clause origSteps[i].hints = true) :
    ∀ (i : Nat) (hi : i < origSteps.size), keep i = true -> ∀ (a : Assignment),
      evalCNF a initCNF = true -> evalClause a origSteps[i].clause = true := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi hki a ha
    have hstepVer := hvalid i hi hki
    have hprev : ∀ j, j < i -> (hj : j < origSteps.size) -> keep j = true ->
        evalClause a origSteps[j].clause = true :=
      fun j hjlt hj hkj => ih j hjlt hj hkj a ha
    have hhints : ∀ hid ∈ origSteps[i].hints, ∀ hClause,
        lookupKept initCNF origSteps keep i hid = some hClause ->
        evalClause a hClause = true :=
      fun hid _ hClause hlu =>
        lookupKept_sat initCNF origSteps keep a ha i hprev hid hClause hlu
    exact checkRupStep_sound a (lookupKept initCNF origSteps keep i)
      origSteps[i].clause origSteps[i].hints hhints hstepVer

/-- Main sparse trimming theorem: any valid backward-reachable RUP sub-trace
    keeping a derived empty clause `[]` witnesses unsatisfiability of `initCNF`. -/
theorem trimLrat_sound (initCNF : CNF) (origSteps : Array LratStep) (keep : Nat -> Bool)
    (hsub : TrimmedLratSubtrace initCNF origSteps keep) :
    Unsat initCNF := by
  rcases hsub.hasEmpty with ⟨k, hkSize, hkk, hkEmpty⟩
  have hkNil : origSteps[k].clause = [] := List.isEmpty_iff.mp hkEmpty
  intro ⟨a, ha⟩
  have hsat := trimmedSubtrace_entailed initCNF origSteps keep hsub.stepsValid k hkSize hkk a ha
  rw [hkNil, evalClause_nil] at hsat
  cases hsat

/-- Strictly ascending list of kept step indices `< origSize`. -/
def keptIndicesList (origSize : Nat) (keep : Nat -> Bool) : List Nat :=
  (List.range origSize).filter keep

/-- Position lookup in a list (`none` if absent). -/
def idxOf (target : Nat) : List Nat -> Option Nat
  | [] => none
  | x :: xs => if x == target then some 0 else (idxOf target xs).map (· + 1)

private def mapListOpt {α β : Type} (f : α -> Option β) : List α -> Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, mapListOpt f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Remap a hint ID from original trace coordinates to compacted sub-trace coordinates. -/
def remapHint (nInit : Nat) (kept : List Nat) (hid : Nat) : Option Nat :=
  if hid < nInit then
    some hid
  else
    (idxOf (hid - nInit) kept).map (fun j' => nInit + j')

/-- Remap all hints of a single LRAT step. -/
def remapStep (nInit : Nat) (kept : List Nat) (st : LratStep) : Option LratStep :=
  match mapListOpt (remapHint nInit kept) st.hints with
  | some hints' => some { clause := st.clause, hints := hints' }
  | none => none

/-- Compact `origSteps` to the kept subset and remap all hints to new indices. -/
def remapTrimmedSteps (initCNF : CNF) (origSteps : Array LratStep)
    (keep : Nat -> Bool) : Option (Array LratStep) :=
  let kept := keptIndicesList origSteps.size keep
  (mapListOpt (fun i =>
    if h : i < origSteps.size then
      remapStep initCNF.length kept origSteps[i]
    else
      none) kept).map List.toArray

private theorem keptIndicesList_pairwise (n : Nat) (keep : Nat -> Bool) :
    (keptIndicesList n keep).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter keep

private theorem mem_keptIndicesList_iff {n : Nat} {keep : Nat -> Bool} {x : Nat} :
    x ∈ keptIndicesList n keep ↔ x < n ∧ keep x = true := by
  simp [keptIndicesList, List.mem_filter, List.mem_range]

private theorem mem_of_idxOf_some {target pos : Nat} :
    ∀ {xs : List Nat}, idxOf target xs = some pos -> target ∈ xs
  | [], h => by cases h
  | x :: xs, h => by
    simp only [idxOf] at h
    split at h
    · next heq =>
      simp only [beq_iff_eq] at heq
      subst heq
      exact List.mem_cons_self ..
    · cases hsub : idxOf target xs with
      | none => rw [hsub] at h; cases h
      | some p => exact List.mem_cons_of_mem x (mem_of_idxOf_some hsub)

private theorem idxOf_of_mem {target : Nat} :
    ∀ {xs : List Nat}, target ∈ xs -> ∃ pos, idxOf target xs = some pos
  | [], h => by cases h
  | x :: xs, h => by
    simp only [idxOf]
    rw [List.mem_cons] at h
    rcases h with rfl | hmem
    · simp
    · split
      · exact ⟨0, rfl⟩
      · obtain ⟨p, hp⟩ := idxOf_of_mem hmem
        exact ⟨p + 1, by simp [hp]⟩

private theorem pairwise_lt_getElem :
    ∀ {xs : List Nat} {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs.Pairwise (· < ·) -> i < j -> xs[i] < xs[j]
  | [], _, _, hi, _, _, _ => by cases hi
  | y :: ys, 0, j + 1, _, hj, hpw, _ => by
    rw [List.pairwise_cons] at hpw
    exact hpw.1 _ (List.getElem_mem (Nat.lt_of_succ_lt_succ hj))
  | _ :: ys, i + 1, j + 1, hi, hj, hpw, hlt => by
    rw [List.pairwise_cons] at hpw
    exact pairwise_lt_getElem (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
      hpw.2 (Nat.lt_of_succ_lt_succ hlt)

private theorem idxOf_getElem_of_pairwise :
    ∀ {xs : List Nat} {x p : Nat},
      xs.Pairwise (· < ·) ->
      idxOf x xs = some p ->
      xs[p]? = some x
  | [], _, _, _, h => by cases h
  | y :: ys, x, p, hpw, h => by
    rw [List.pairwise_cons] at hpw
    simp only [idxOf] at h
    split at h
    · next heq =>
      simp only [beq_iff_eq] at heq
      simp only [Option.some.injEq] at h
      subst heq; subst h; rfl
    · cases hsub : idxOf x ys with
      | none => rw [hsub] at h; cases h
      | some p' =>
        rw [hsub] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [List.getElem?_cons_succ]
        exact idxOf_getElem_of_pairwise hpw.2 hsub

private theorem idxOf_lt_of_pairwise :
    ∀ {xs : List Nat} {a b pa pb : Nat},
      xs.Pairwise (· < ·) ->
      idxOf a xs = some pa ->
      idxOf b xs = some pb ->
      a < b ->
      pa < pb
  | [], _, _, _, _, _, ha, _, _ => by cases ha
  | y :: ys, a, b, pa, pb, hpw, ha, hb, hlt => by
    rw [List.pairwise_cons] at hpw
    simp only [idxOf] at ha hb
    split at ha
    · next hya =>
      simp only [beq_iff_eq] at hya
      have hyb : (y == b) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp only [hyb, Bool.false_eq_true, ↓reduceIte] at hb
      simp only [Option.some.injEq] at ha
      cases hsubB : idxOf b ys with
      | none => rw [hsubB] at hb; cases hb
      | some pb' =>
        rw [hsubB] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        omega
    · next hya =>
      have hyane : y ≠ a := fun heq => hya (by simp [heq])
      cases hsubA : idxOf a ys with
      | none => rw [hsubA] at ha; cases ha
      | some pa' =>
        rw [hsubA] at ha
        simp only [Option.map_some, Option.some.injEq] at ha
        have haMem : a ∈ ys := mem_of_idxOf_some hsubA
        have hyaLt : y < a := hpw.1 a haMem
        have hyb : (y == b) = false := by
          rw [beq_eq_false_iff_ne]
          omega
        simp only [hyb, Bool.false_eq_true, ↓reduceIte] at hb
        cases hsubB : idxOf b ys with
        | none => rw [hsubB] at hb; cases hb
        | some pb' =>
          rw [hsubB] at hb
          simp only [Option.map_some, Option.some.injEq] at hb
          have ih := idxOf_lt_of_pairwise hpw.2 hsubA hsubB hlt
          omega

private theorem mapListOpt_exists {α β : Type} (f : α -> Option β) :
    ∀ (xs : List α),
      (∀ x ∈ xs, ∃ y, f x = some y) ->
      ∃ ys, mapListOpt f xs = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, hf => by
    obtain ⟨y, hy⟩ := hf x (List.mem_cons_self ..)
    obtain ⟨ys, hys⟩ := mapListOpt_exists f xs (fun a ha => hf a (List.mem_cons_of_mem x ha))
    exact ⟨y :: ys, by simp [mapListOpt, hy, hys]⟩

private theorem mapListOpt_length {α β : Type} (f : α -> Option β) :
    ∀ {xs : List α} {ys : List β},
      mapListOpt f xs = some ys -> ys.length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by
    simp only [mapListOpt] at h
    split at h <;> cases h
  | x :: xs, y :: ys, h => by
    simp only [mapListOpt] at h
    split at h
    · simp only [Option.some.injEq, List.cons.injEq] at h
      next _ ys' _ hys =>
      rcases h with ⟨_, rfl⟩
      simp [mapListOpt_length f hys]
    · cases h

private theorem mapListOpt_getElem? {α β : Type} (f : α -> Option β) :
    ∀ {xs : List α} {ys : List β},
      mapListOpt f xs = some ys ->
      ∀ (p : Nat) (x : α), xs[p]? = some x -> ∃ y, ys[p]? = some y ∧ f x = some y
  | [], _, _, _, _, hx => by cases hx
  | x₀ :: xs, ys, hmap, p, x, hx => by
    simp only [mapListOpt] at hmap
    split at hmap
    · next y₀ ys' hy₀ hys' =>
      simp only [Option.some.injEq] at hmap
      subst hmap
      cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨y₀, rfl, hy₀⟩
      | succ p' =>
        exact mapListOpt_getElem? f hys' p' x hx
    · cases hmap

private theorem rupPropagate_map (lookup₁ lookup₂ : Nat -> Option Clause)
    (g : Nat -> Option Nat) :
    ∀ (hs hs' : List Nat) (units : List Lit),
      mapListOpt g hs = some hs' ->
      (∀ hid ∈ hs, ∀ hid', g hid = some hid' -> lookup₂ hid' = lookup₁ hid) ->
      rupPropagate lookup₂ units hs' = rupPropagate lookup₁ units hs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by
    simp only [mapListOpt] at h
    split at h <;> cases h
  | hid :: hs, hid' :: hs', units, hmap, hlu => by
    simp only [mapListOpt] at hmap
    split at hmap
    · next y ys hy hys =>
      simp only [Option.some.injEq, List.cons.injEq] at hmap
      rcases hmap with ⟨rfl, rfl⟩
      have heq := hlu hid (List.mem_cons_self ..) y hy
      simp only [rupPropagate, heq]
      cases hlu1 : lookup₁ hid with
      | none => rfl
      | some hc =>
        simp only
        cases evalHintUnder units hc with
        | conflict => rfl
        | invalid => rfl
        | unit u =>
          exact rupPropagate_map lookup₁ lookup₂ g hs ys (u :: units) hys
            (fun a ha a' ha' => hlu a (List.mem_cons_of_mem hid ha) a' ha')
    · cases hmap

/-- Backward hint-closure condition ensuring every hint referenced by a kept step
    is either an original CNF clause or an earlier kept step (`j < i ∧ keep j = true`). -/
def BackwardHintsClosed (initCNF : CNF) (origSteps : Array LratStep)
    (keep : Nat -> Bool) : Prop :=
  ∀ (i : Nat) (hi : i < origSteps.size), keep i = true ->
    ∀ hid ∈ origSteps[i].hints,
      hid < initCNF.length ∨ (hid - initCNF.length < i ∧ keep (hid - initCNF.length) = true)

private theorem remapStep_clause {nInit : Nat} {kept : List Nat} {orig st : LratStep}
    (h : remapStep nInit kept orig = some st) : st.clause = orig.clause := by
  unfold remapStep at h
  cases hm : mapListOpt (remapHint nInit kept) orig.hints <;> rw [hm] at h
  · cases h
  · simp only [Option.some.injEq] at h
    rw [← h]

/-- Compaction correctness: any `TrimmedLratSubtrace` that is backward-closed on its
    hints remaps to a dense self-contained `trimmedSteps` accepted by `verifyParallelLRAT`. -/
theorem remapTrimmedSteps_verify (initCNF : CNF) (origSteps : Array LratStep)
    (keep : Nat -> Bool)
    (hsub : TrimmedLratSubtrace initCNF origSteps keep)
    (hclosed : BackwardHintsClosed initCNF origSteps keep) :
    ∃ trimmedSteps : Array LratStep,
      remapTrimmedSteps initCNF origSteps keep = some trimmedSteps ∧
      verifyParallelLRAT initCNF trimmedSteps = true := by
  let kept := keptIndicesList origSteps.size keep
  have hpw : kept.Pairwise (· < ·) := keptIndicesList_pairwise origSteps.size keep
  let f : Nat -> Option LratStep := fun i =>
    if h : i < origSteps.size then
      remapStep initCNF.length kept origSteps[i]
    else
      none
  have hstepExists : ∀ i ∈ kept, ∃ st, f i = some st := by
    intro i hiMem
    obtain ⟨hiSize, hki⟩ := mem_keptIndicesList_iff.mp hiMem
    have hHintsSome : ∀ hid ∈ origSteps[i].hints,
        ∃ hid', remapHint initCNF.length kept hid = some hid' := by
      intro hid hhid
      rcases hclosed i hiSize hki hid hhid with hinit | ⟨hjlt, hkj⟩
      · exact ⟨hid, by simp [remapHint, hinit]⟩
      · have hjMem : hid - initCNF.length ∈ kept :=
          mem_keptIndicesList_iff.mpr ⟨by omega, hkj⟩
        obtain ⟨pj, hpj⟩ := idxOf_of_mem hjMem
        by_cases hlt : hid < initCNF.length
        · exact ⟨hid, by simp [remapHint, hlt]⟩
        · exact ⟨initCNF.length + pj, by simp [remapHint, hlt, hpj]⟩
    obtain ⟨hints', hhints'⟩ := mapListOpt_exists (remapHint initCNF.length kept)
      origSteps[i].hints hHintsSome
    refine ⟨{ clause := origSteps[i].clause, hints := hints' }, ?_⟩
    simp [f, hiSize, remapStep, hhints']
  obtain ⟨tsList, htsList⟩ := mapListOpt_exists f kept hstepExists
  refine ⟨tsList.toArray, ?_, ?_⟩
  · simp [remapTrimmedSteps, kept, f, htsList]
  · have hlen : tsList.length = kept.length := mapListOpt_length f htsList
    unfold verifyParallelLRAT
    rw [Bool.and_eq_true]
    constructor
    · unfold verifyAllSteps
      rw [List.all_eq_true]
      intro ni hniRange
      rw [List.mem_range, List.size_toArray] at hniRange
      have hniKeptLen : ni < kept.length := by rw [← hlen]; exact hniRange
      have hgetKept : kept[ni]? = some kept[ni] := List.getElem?_eq_getElem hniKeptLen
      obtain ⟨st, hstSome, hfst⟩ := mapListOpt_getElem? f htsList ni kept[ni] hgetKept
      have hstEq : tsList.toArray[ni]'(by rw [List.size_toArray]; exact hniRange) = st := by
        rw [List.getElem_toArray]
        have : tsList[ni]? = some tsList[ni] := List.getElem?_eq_getElem hniRange
        rw [hstSome] at this
        exact (Option.some.inj this).symm
      have hiMem : kept[ni] ∈ kept := List.getElem_mem hniKeptLen
      obtain ⟨hiSize, hki⟩ := mem_keptIndicesList_iff.mp hiMem
      simp only [f, hiSize, ↓reduceDIte] at hfst
      unfold remapStep at hfst
      cases hmapH : mapListOpt (remapHint initCNF.length kept) origSteps[kept[ni]].hints with
      | none => rw [hmapH] at hfst; cases hfst
      | some hints' =>
        rw [hmapH] at hfst
        simp only [Option.some.injEq] at hfst
        have hstClause : st.clause = origSteps[kept[ni]].clause := by rw [← hfst]
        have hstHints : st.hints = hints' := by rw [← hfst]
        have hniIdx : idxOf kept[ni] kept = some ni := by
          obtain ⟨p, hp⟩ := idxOf_of_mem hiMem
          have hpget := idxOf_getElem_of_pairwise hpw hp
          have hpsize : p < kept.length := by
            by_cases hlt : p < kept.length
            · exact hlt
            · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hpget
              cases hpget
          have hpeq : kept[p] = kept[ni] := by
            rw [List.getElem?_eq_getElem hpsize] at hpget
            exact Option.some.inj hpget
          have hpni : p = ni := by
            by_cases hlt1 : p < ni
            · have := pairwise_lt_getElem hpsize hniKeptLen hpw hlt1; omega
            · by_cases hlt2 : ni < p
              · have := pairwise_lt_getElem hniKeptLen hpsize hpw hlt2; omega
              · omega
          subst hpni; exact hp
        have hlookupEq : ∀ hid ∈ origSteps[kept[ni]].hints, ∀ hid',
            remapHint initCNF.length kept hid = some hid' ->
            lookupCausal initCNF tsList.toArray ni hid' =
              lookupKept initCNF origSteps keep kept[ni] hid := by
          intro hid _ hid' hrem
          unfold remapHint at hrem
          split at hrem
          · next hlt =>
            simp only [Option.some.injEq] at hrem
            subst hrem
            simp [lookupCausal, lookupKept, hlt]
          · next hnlt =>
            cases hidxJ : idxOf (hid - initCNF.length) kept with
            | none => rw [hidxJ] at hrem; cases hrem
            | some nj =>
              rw [hidxJ] at hrem
              simp only [Option.map_some, Option.some.injEq] at hrem
              subst hrem
              have hnlt2 : ¬ (initCNF.length + nj < initCNF.length) := by omega
              have hsub2 : initCNF.length + nj - initCNF.length = nj := by omega
              have hjMem : hid - initCNF.length ∈ kept := mem_of_idxOf_some hidxJ
              obtain ⟨hjSize, hkj⟩ := mem_keptIndicesList_iff.mp hjMem
              simp only [lookupCausal, lookupKept, hnlt, hnlt2, hsub2, ↓reduceIte]
              by_cases hjlt : hid - initCNF.length < kept[ni]
              · have hnjlt : nj < ni := idxOf_lt_of_pairwise hpw hidxJ hniIdx hjlt
                have hnjLen : nj < tsList.length := by omega
                have hnjArr : nj < tsList.toArray.size := by
                  rw [List.size_toArray]; exact hnjLen
                have hjGet : kept[nj]? = some (hid - initCNF.length) :=
                  idxOf_getElem_of_pairwise hpw hidxJ
                obtain ⟨stJ, hstJSome, hfstJ⟩ := mapListOpt_getElem? f htsList nj _ hjGet
                have hstJClause : stJ.clause = origSteps[hid - initCNF.length].clause := by
                  simp only [f, hjSize, ↓reduceDIte] at hfstJ
                  exact remapStep_clause hfstJ
                have htsArrEq : tsList.toArray[nj] = stJ := by
                  rw [List.getElem_toArray]
                  have : tsList[nj]? = some tsList[nj] := List.getElem?_eq_getElem hnjLen
                  rw [hstJSome] at this
                  exact (Option.some.inj this).symm
                simp only [hjlt, hkj, hjSize, hnjlt, hnjArr, decide_true, Bool.and_true, ↓reduceIte,
                  ↓reduceDIte, htsArrEq, hstJClause]
              · have hninj : ¬ nj < ni := by
                  intro hnjlt
                  have hge : kept[ni] ≤ hid - initCNF.length := Nat.le_of_not_lt hjlt
                  have hgetJ : kept[nj]? = some (hid - initCNF.length) :=
                    idxOf_getElem_of_pairwise hpw hidxJ
                  have hnjKept : nj < kept.length := by omega
                  rw [List.getElem?_eq_getElem hnjKept] at hgetJ
                  have hltStep := pairwise_lt_getElem hnjKept hniKeptLen hpw hnjlt
                  have := Option.some.inj hgetJ
                  omega
                simp [hjlt, hninj]
        have hniArr : ni < tsList.toArray.size := by rw [List.size_toArray]; exact hniRange
        simp only [hniArr, ↓reduceDIte]
        rw [hstEq]
        unfold verifyStep checkRupStep
        rw [hstClause, hstHints]
        rw [rupPropagate_map (lookupKept initCNF origSteps keep kept[ni])
          (lookupCausal initCNF tsList.toArray ni) (remapHint initCNF.length kept)
          origSteps[kept[ni]].hints hints' (origSteps[kept[ni]].clause.map Lit.neg) hmapH hlookupEq]
        exact hsub.stepsValid kept[ni] hiSize hki
    · rcases hsub.hasEmpty with ⟨k, hkSize, hkk, hkEmpty⟩
      have hkMem : k ∈ kept := mem_keptIndicesList_iff.mpr ⟨hkSize, hkk⟩
      obtain ⟨nk, hnk⟩ := idxOf_of_mem hkMem
      have hkGet : kept[nk]? = some k := idxOf_getElem_of_pairwise hpw hnk
      have hnkKept : nk < kept.length := by
        by_cases hlt : nk < kept.length
        · exact hlt
        · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hkGet
          cases hkGet
      have hnkLen : nk < tsList.length := by rw [hlen]; exact hnkKept
      have hnkArr : nk < tsList.toArray.size := by rw [List.size_toArray]; exact hnkLen
      obtain ⟨stK, hstKSome, hfstK⟩ := mapListOpt_getElem? f htsList nk k hkGet
      have hstKClause : stK.clause = origSteps[k].clause := by
        simp only [f, hkSize, ↓reduceDIte] at hfstK
        exact remapStep_clause hfstK
      have htsK : tsList.toArray[nk] = stK := by
        rw [List.getElem_toArray]
        have : tsList[nk]? = some tsList[nk] := List.getElem?_eq_getElem hnkLen
        rw [hstKSome] at this
        exact (Option.some.inj this).symm
      rw [List.any_eq_true]
      refine ⟨nk, List.mem_range.mpr hnkArr, ?_⟩
      simp only [hnkArr, ↓reduceDIte, htsK, hstKClause, hkEmpty]

/-- Compacted LRAT trimming soundness: if compacted `trimmedSteps` produced by
    `remapTrimmedSteps` passes `verifyParallelLRAT`, `initCNF` is unsatisfiable. -/
theorem trimLrat_remap_sound (initCNF : CNF) (origSteps trimmedSteps : Array LratStep)
    (keep : Nat -> Bool)
    (_hremap : remapTrimmedSteps initCNF origSteps keep = some trimmedSteps)
    (hver : verifyParallelLRAT initCNF trimmedSteps = true) :
    Unsat initCNF :=
  gpu_parallel_lrat_unsat initCNF trimmedSteps hver

end ConGpuProof
