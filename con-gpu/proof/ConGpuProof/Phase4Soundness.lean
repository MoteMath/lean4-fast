/-
ConGpuProof.Phase4Soundness
===========================
Formal Lean 4 verification for con-gpu Phase 4 extensions:
  1. Paged 8 GiB SoA Arena (`PAGE_WORDS = 2^28`, `8` pages = `2^31` `u32` words total):
     `pagedArenaPage_lt_eight`, `pagedArenaOffset_lt_pageCap`,
     `pagedArenaAddr_bijective`, `pagedArenaLookup_sound`.
  2. Persistent GPU Work-Queue & Tier-2 Promotion:
     `tier2BudgetPromotion_sound`, `twoEndedWorkStealing_sound`.
  3. Wider Exact WGSL Reductions (little-endian base-`2^32` limbs, `String` words, `k`-field eta):
     `multiLimbNatAdd_correct`, `multiLimbNatSub_correct`, `multiLimbNatMul_correct`,
     `multiLimbNatBeq_correct`, `multiLimbNatBle_correct`,
     `stringLitWordsEq_sound`, `multiFieldStructEta_sound`.
  4. `CGSNAP03` Stat Manifest & Split GPU-First Load:
     `cgsnap03StatManifest_sound`, `cgsnap03SplitLoad_sound`.
-/

import ConGpuProof.Phase3Soundness

namespace ConGpuProof

/-! ### 1. Paged 8 GiB SoA Arena (`PAGE_WORDS = 2^28`, 8 pages = `2^31` words) -/

/-- Number of 32-bit words per GPU arena page (`2^28` words = `1 GiB`). -/
def pageWords : Nat := 2 ^ 28

/-- Maximum addressable 32-bit words across 8 GPU arena pages (`2^31` words = `8 GiB`). -/
def maxPagedWords : Nat := 2 ^ 31

private theorem eight_mul_pageWords : 8 * pageWords = maxPagedWords := by decide

/-- **Theorem (`pagedArenaPage_lt_eight`)**:
    Every word index `< 2^31` maps to a page index `< 8`. -/
theorem pagedArenaPage_lt_eight :
    ∀ idx : Nat, idx < 2 ^ 31 -> idx / 2 ^ 28 < 8 := by
  intro idx hidx
  have hpow : 8 * 2 ^ 28 = 2 ^ 31 := by decide
  rw [← hpow] at hidx
  exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hidx

/-- **Theorem (`pagedArenaOffset_lt_pageCap`)**:
    Every word index `< 2^31` has an intra-page offset `< 2^28`. -/
theorem pagedArenaOffset_lt_pageCap :
    ∀ idx : Nat, idx < 2 ^ 31 -> idx % 2 ^ 28 < 2 ^ 28 := by
  intro idx _
  exact Nat.mod_lt idx (by decide)

private theorem paged_pair_inj {p1 o1 p2 o2 M : Nat} (hM : 0 < M)
    (ho1 : o1 < M) (ho2 : o2 < M)
    (heq : p1 * M + o1 = p2 * M + o2) : p1 = p2 ∧ o1 = o2 := by
  have hdiv : (p1 * M + o1) / M = (p2 * M + o2) / M := congrArg (· / M) heq
  rw [Nat.add_comm (p1 * M) o1, Nat.add_comm (p2 * M) o2] at hdiv
  rw [Nat.add_mul_div_right _ _ hM, Nat.add_mul_div_right _ _ hM] at hdiv
  rw [Nat.div_eq_of_lt ho1, Nat.div_eq_of_lt ho2, Nat.zero_add, Nat.zero_add] at hdiv
  refine ⟨hdiv, ?_⟩
  rw [hdiv] at heq
  exact Nat.add_left_cancel heq

/-- **Theorem (`pagedArenaAddr_bijective`)**:
    Page/offset decomposition `(idx / 2^28, idx % 2^28)` reconstructs `idx` and
    is injective over `p < 8, o < 2^28`. -/
theorem pagedArenaAddr_bijective :
    (∀ idx : Nat, (idx / 2 ^ 28) * 2 ^ 28 + idx % 2 ^ 28 = idx) ∧
    (∀ p1 o1 p2 o2 : Nat,
      p1 < 8 -> o1 < 2 ^ 28 -> p2 < 8 -> o2 < 2 ^ 28 ->
      p1 * 2 ^ 28 + o1 = p2 * 2 ^ 28 + o2 ->
      p1 = p2 ∧ o1 = o2) := by
  refine ⟨?_, ?_⟩
  · intro idx
    rw [Nat.mul_comm, Nat.div_add_mod]
  · intro p1 o1 p2 o2 _ ho1 _ ho2 heq
    exact paged_pair_inj (by decide) ho1 ho2 heq

/-- Splits a flat `UInt32` arena buffer of up to `2^31` words into `8` slices of `2^28` words. -/
def mkPagedArena (buf : Array UInt32) : Array (Array UInt32) :=
  Array.ofFn (fun p : Fin 8 =>
    buf.extract (p.1 * pageWords) ((p.1 + 1) * pageWords))

/-- Two-level page-directory lookup `pages[idx / 2^28][idx % 2^28]`. -/
def pagedLookup (pages : Array (Array UInt32)) (idx : Nat) : Option UInt32 :=
  (pages[idx / pageWords]?).bind (fun pg => pg[idx % pageWords]?)

/-- General relational characterization of an 8-page split of a flat `UInt32` arena. -/
def PagedArenaSplit (buf : Array UInt32) (pages : Array (Array UInt32)) : Prop :=
  pages.size = 8 ∧
  ∀ p, p < 8 -> ∀ o, o < pageWords -> p * pageWords + o < buf.size ->
    ∃ pg, pages[p]? = some pg ∧ pg[o]? = buf[p * pageWords + o]?

theorem mkPagedArena_isSplit (buf : Array UInt32) :
    PagedArenaSplit buf (mkPagedArena buf) := by
  refine ⟨by simp [mkPagedArena], ?_⟩
  intro p hp o ho hlt
  let pg := buf.extract (p * pageWords) ((p + 1) * pageWords)
  have hpsize : p < (mkPagedArena buf).size := by simpa [mkPagedArena] using hp
  have hgetp : (mkPagedArena buf)[p]? = some pg := by
    rw [Array.getElem?_eq_getElem hpsize]
    simp [mkPagedArena, pg]
  have hadd : p * pageWords + o < (p + 1) * pageWords := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left ho _
  have hmin : p * pageWords + o < min ((p + 1) * pageWords) buf.size :=
    Nat.lt_min.mpr ⟨hadd, hlt⟩
  have hpg_lt : o < pg.size := by
    dsimp [pg]
    rw [Array.size_extract]
    exact Nat.lt_sub_of_add_lt (by rw [Nat.add_comm]; exact hmin)
  refine ⟨pg, hgetp, ?_⟩
  rw [Array.getElem?_eq_getElem hpg_lt, Array.getElem?_eq_getElem hlt]
  dsimp [pg]
  rw [Array.getElem_extract]

/-- **Theorem (`pagedArenaLookup_sound`)**:
    Two-level paged lookup `pages[idx / 2^28][idx % 2^28]` agrees identically with
    flat indexing `buf[idx]?` for every `buf.size ≤ 2^31` and `idx < buf.size`
    (both for any `PagedArenaSplit` and specifically for `mkPagedArena buf`). -/
theorem pagedArenaLookup_sound
    {buf : Array UInt32} {pages : Array (Array UInt32)} {idx : Nat}
    (hsplit : PagedArenaSplit buf pages)
    (hsz : buf.size ≤ 2 ^ 31)
    (hidx : idx < buf.size) :
    pagedLookup pages idx = buf[idx]? ∧
    pagedLookup (mkPagedArena buf) idx = some buf[idx] := by
  have h31 : idx < 2 ^ 31 := Nat.lt_of_lt_of_le hidx hsz
  have hp : idx / 2 ^ 28 < 8 := pagedArenaPage_lt_eight idx h31
  have ho : idx % 2 ^ 28 < 2 ^ 28 := pagedArenaOffset_lt_pageCap idx h31
  have haddr : (idx / 2 ^ 28) * 2 ^ 28 + idx % 2 ^ 28 = idx :=
    pagedArenaAddr_bijective.1 idx
  have hlt_addr : (idx / pageWords) * pageWords + idx % pageWords < buf.size := by
    change (idx / 2 ^ 28) * 2 ^ 28 + idx % 2 ^ 28 < buf.size
    rw [haddr]; exact hidx
  have hsplit_self := mkPagedArena_isSplit buf
  constructor
  · obtain ⟨pg, hpg, hgeto⟩ := hsplit.2 (idx / pageWords) hp (idx % pageWords) ho hlt_addr
    unfold pagedLookup
    rw [hpg]
    dsimp only [Option.bind]
    rw [hgeto]
    change buf[(idx / 2 ^ 28) * 2 ^ 28 + idx % 2 ^ 28]? = buf[idx]?
    rw [haddr]
  · obtain ⟨pg, hpg, hgeto⟩ := hsplit_self.2 (idx / pageWords) hp (idx % pageWords) ho hlt_addr
    unfold pagedLookup
    rw [hpg]
    dsimp only [Option.bind]
    rw [hgeto]
    change buf[(idx / 2 ^ 28) * 2 ^ 28 + idx % 2 ^ 28]? = some buf[idx]
    rw [haddr, Array.getElem?_eq_getElem hidx]


/-! ### 2. Persistent GPU Work-Queue & Tier-2 Promotion -/

/-- Tier-1 delegation reason codes matching `typecheck_arena.wgsl`. -/
def reasonStepBudget : Nat := 3
def reasonStackBudget : Nat := 4
def reasonScratchBudget : Nat := 5

/-- Tier-1 job promotion guard: active quantum-cutoff (`status = 0`) or budget exhaustion
    (`reasonStepBudget = 3`, `reasonStackBudget = 4`, `reasonScratchBudget = 5`). -/
def isTier2Promotable (status reason : Nat) : Bool :=
  status == 0 || reason == reasonStepBudget ||
    reason == reasonStackBudget || reason == reasonScratchBudget

/-- Per-job result record capturing promotion, host delegation, and final acceptance. -/
structure TieredJobVerdict where
  tier2Promoted : Bool
  hostDelegated : Bool
  accepted : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Evaluates a single job across Tier 1 WGSL -> optional Tier 2 WGSL -> exact host checker.
    Status encoding: `0` = running/quantum-cutoff, `1` = accepted, `2` = rejected, `3` = delegated. -/
def evalJobTiered (t1Status t1Reason t2Status : Nat) (hostCheck : Bool) : TieredJobVerdict :=
  if t1Status == 1 then
    { tier2Promoted := false, hostDelegated := false, accepted := true }
  else if t1Status == 2 then
    { tier2Promoted := false, hostDelegated := false, accepted := false }
  else if isTier2Promotable t1Status t1Reason then
    if t2Status == 1 then
      { tier2Promoted := true, hostDelegated := false, accepted := true }
    else if t2Status == 2 then
      { tier2Promoted := true, hostDelegated := false, accepted := false }
    else
      { tier2Promoted := true, hostDelegated := true, accepted := hostCheck }
  else
    { tier2Promoted := false, hostDelegated := true, accepted := hostCheck }

/-- Batch summary of evaluating `[0..n)` through Tier 1 -> Tier 2 promotion -> exact host. -/
structure TieredBatchSummary where
  processed : Nat
  acceptedCount : Nat
  rejectedCount : Nat
  allAccepted : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Evaluates all jobs `0..n-1` once each in sequence, recording exact counts. -/
def runTieredBatch (t1Status t1Reason t2Status : Nat -> Nat) (hostCheck : Nat -> Bool) :
    Nat -> TieredBatchSummary
  | 0 => { processed := 0, acceptedCount := 0, rejectedCount := 0, allAccepted := true }
  | n + 1 =>
    let prev := runTieredBatch t1Status t1Reason t2Status hostCheck n
    let v := evalJobTiered (t1Status n) (t1Reason n) (t2Status n) (hostCheck n)
    { processed := prev.processed + 1
      acceptedCount := prev.acceptedCount + if v.accepted then 1 else 0
      rejectedCount := prev.rejectedCount + if v.accepted then 0 else 1
      allAccepted := prev.allAccepted && v.accepted }

private theorem evalJobTiered_sound_single
    {t1s t1r t2s : Nat} {host isValid : Bool}
    (ht1Acc : t1s = 1 -> isValid = true)
    (ht1Rej : t1s = 2 -> isValid = false)
    (ht2Acc : t2s = 1 -> isValid = true)
    (ht2Rej : t2s = 2 -> isValid = false)
    (hhost : host = isValid) :
    (evalJobTiered t1s t1r t2s host).accepted = isValid ∧
    ((t1s ≠ 1 ∧ t1s ≠ 2 ∧ (t1s = 0 ∨ t1r = 3 ∨ t1r = 4 ∨ t1r = 5)) ->
      (evalJobTiered t1s t1r t2s host).tier2Promoted = true ∧
      (t2s ≠ 1 ∧ t2s ≠ 2 -> (evalJobTiered t1s t1r t2s host).hostDelegated = true)) := by
  unfold evalJobTiered isTier2Promotable
  refine ⟨?_, ?_⟩
  · by_cases h11 : t1s == 1
    · simp only [h11, ↓reduceIte]; exact (ht1Acc (beq_iff_eq.mp h11)).symm
    · simp only [h11, Bool.false_eq_true, ↓reduceIte]
      by_cases h12 : t1s == 2
      · simp only [h12, ↓reduceIte]; exact (ht1Rej (beq_iff_eq.mp h12)).symm
      · simp only [h12, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (t1s == 0 || t1r == reasonStepBudget ||
            t1r == reasonStackBudget || t1r == reasonScratchBudget) = true
        · simp only [hp, ↓reduceIte]
          by_cases h21 : t2s == 1
          · simp only [h21, ↓reduceIte]; exact (ht2Acc (beq_iff_eq.mp h21)).symm
          · simp only [h21, Bool.false_eq_true, ↓reduceIte]
            by_cases h22 : t2s == 2
            · simp only [h22, ↓reduceIte]; exact (ht2Rej (beq_iff_eq.mp h22)).symm
            · simp only [h22, Bool.false_eq_true, ↓reduceIte]; exact hhost
        · simp only [hp]; exact hhost
  · rintro ⟨hne1, hne2, htrig⟩
    have h11 : (t1s == 1) = false := beq_false_of_ne hne1
    have h12 : (t1s == 2) = false := beq_false_of_ne hne2
    have htrig' : (t1s == 0 || t1r == reasonStepBudget ||
        t1r == reasonStackBudget || t1r == reasonScratchBudget) = true := by
      rcases htrig with h | h | h | h
      · simp [h]
      · simp [h, reasonStepBudget]
      · simp [h, reasonStackBudget]
      · simp [h, reasonScratchBudget]
    simp only [h11, h12, Bool.false_eq_true, ↓reduceIte, htrig']
    by_cases h21 : t2s = 1
    · simp only [beq_iff_eq.mpr h21, ↓reduceIte]
      refine ⟨trivial, fun h => absurd h21 h.1⟩
    · have hb21 : (t2s == 1) = false := beq_false_of_ne h21
      simp only [hb21, Bool.false_eq_true, ↓reduceIte]
      by_cases h22 : t2s = 2
      · simp only [beq_iff_eq.mpr h22, ↓reduceIte]
        refine ⟨trivial, fun h => absurd h22 h.2⟩
      · have hb22 : (t2s == 2) = false := beq_false_of_ne h22
        simp only [hb22, Bool.false_eq_true, ↓reduceIte]
        exact ⟨trivial, fun _ => trivial⟩

/-- **Theorem (`tier2BudgetPromotion_sound`)**:
    Promoting `status = 0` or `REASON_{STEP,STACK,SCRATCH}_BUDGET` (`3, 4, 5`) from Tier 1 to
    Tier 2 WGSL (with any non-accepted Tier-2 job delegated to exact host checking) preserves
    total soundness, processes every job in `[0..n)` without drops or double-accepts, and rejects
    whenever any job is invalid. -/
theorem tier2BudgetPromotion_sound
    (n : Nat) (t1Status t1Reason t2Status : Nat -> Nat)
    (hostCheck isValid : Nat -> Bool)
    (ht1Acc : ∀ i < n, t1Status i = 1 -> isValid i = true)
    (ht1Rej : ∀ i < n, t1Status i = 2 -> isValid i = false)
    (ht2Acc : ∀ i < n, t2Status i = 1 -> isValid i = true)
    (ht2Rej : ∀ i < n, t2Status i = 2 -> isValid i = false)
    (hhost : ∀ i < n, hostCheck i = isValid i) :
    let sum := runTieredBatch t1Status t1Reason t2Status hostCheck n
    sum.processed = n ∧
    sum.acceptedCount + sum.rejectedCount = n ∧
    (sum.allAccepted = true ↔ ∀ i < n, isValid i = true) ∧
    (∀ i < n, t1Status i ≠ 1 -> t1Status i ≠ 2 ->
      (t1Status i = 0 ∨ t1Reason i = 3 ∨ t1Reason i = 4 ∨ t1Reason i = 5) ->
      (evalJobTiered (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).tier2Promoted = true ∧
      (t2Status i ≠ 1 -> t2Status i ≠ 2 ->
        (evalJobTiered (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).hostDelegated = true)) ∧
    (∀ i < n, isValid i = false ->
      (evalJobTiered (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).accepted = false ∧
      sum.allAccepted = false) := by
  induction n with
  | zero =>
    dsimp only [runTieredBatch]
    refine ⟨rfl, rfl, ⟨(fun _ _ hi => absurd hi (Nat.not_lt_zero _)), (fun _ => rfl)⟩,
            (fun _ hi => absurd hi (Nat.not_lt_zero _)), (fun _ hi => absurd hi (Nat.not_lt_zero _))⟩
  | succ k ih =>
    have ih' := ih
      (fun i hi => ht1Acc i (Nat.lt_succ_of_lt hi))
      (fun i hi => ht1Rej i (Nat.lt_succ_of_lt hi))
      (fun i hi => ht2Acc i (Nat.lt_succ_of_lt hi))
      (fun i hi => ht2Rej i (Nat.lt_succ_of_lt hi))
      (fun i hi => hhost i (Nat.lt_succ_of_lt hi))
    dsimp only at ih'
    dsimp only [runTieredBatch]
    obtain ⟨hproc, hcnt, hall, hprom, hrej⟩ := ih'
    have hlast := @evalJobTiered_sound_single
      (t1Status k) (t1Reason k) (t2Status k) (hostCheck k) (isValid k)
      (ht1Acc k (Nat.lt_succ_self k))
      (ht1Rej k (Nat.lt_succ_self k))
      (ht2Acc k (Nat.lt_succ_self k))
      (ht2Rej k (Nat.lt_succ_self k))
      (hhost k (Nat.lt_succ_self k))
    let v := evalJobTiered (t1Status k) (t1Reason k) (t2Status k) (hostCheck k)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hproc]
    · cases v.accepted <;> simp <;> omega
    · constructor
      · intro hband i hi
        simp only [Bool.and_eq_true] at hband
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact hall.1 hband.1 i hlt
        · rw [← hlast.1]; exact hband.2
      · intro hvalid
        simp only [Bool.and_eq_true]
        refine ⟨hall.2 (fun i hi => hvalid i (Nat.lt_succ_of_lt hi)), ?_⟩
        rw [hlast.1]
        exact hvalid k (Nat.lt_succ_self k)
    · intro i hi hne1 hne2 htrig
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hprom i hlt hne1 hne2 htrig
      · have hp := hlast.2 ⟨hne1, hne2, htrig⟩
        exact ⟨hp.1, fun h1 h2 => hp.2 ⟨h1, h2⟩⟩
    · intro i hi hbad
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · obtain ⟨hv_i, hsum_k⟩ := hrej i hlt hbad
        refine ⟨hv_i, ?_⟩
        simp [hsum_k]
      · have hv_k : (evalJobTiered (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).accepted = false := by
          rw [hlast.1]; exact hbad
        refine ⟨hv_k, ?_⟩
        rw [hv_k]
        exact Bool.and_false _

/-- Persistent two-ended GPU/CPU work-queue state over `[0, totalJobs)`. -/
structure WorkQueueState where
  totalJobs : Nat
  front : Nat
  back : Nat
  verifiedCount : Nat
  allOk : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Initial work-queue state covering `[0, m)`. -/
def WorkQueueState.init (m : Nat) : WorkQueueState :=
  { totalJobs := m, front := 0, back := m, verifiedCount := 0, allOk := true }

/-- Scheduling event for persistent work-queue workers. -/
inductive QueueAction where
  | gpuClaim (batch : Nat)
  | cpuSteal (batch : Nat)
  deriving DecidableEq, Repr, Inhabited

private def checkRangeBool (ok : Nat -> Bool) : Nat -> Nat -> Bool
  | _, 0 => true
  | start, len + 1 => ok start && checkRangeBool ok (start + 1) len

private theorem checkRangeBool_iff (ok : Nat -> Bool) (start len : Nat) :
    checkRangeBool ok start len = true ↔
      ∀ j, start ≤ j -> j < start + len -> ok j = true := by
  induction len generalizing start with
  | zero =>
    simp [checkRangeBool]; omega
  | succ k ih =>
    unfold checkRangeBool
    simp only [Bool.and_eq_true, ih (start + 1)]
    constructor
    · rintro ⟨hs, hrest⟩ j hlo hhi
      by_cases hjeq : j = start
      · subst hjeq; exact hs
      · exact hrest j (by omega) (by omega)
    · intro hall
      exact ⟨hall start (Nat.le_refl _) (by omega),
             fun j hlo hhi => hall j (by omega) (by omega)⟩

/-- Executes one GPU front-claim or CPU back-steal batch on `st`. -/
def stepWorkQueue (gpuOk cpuOk : Nat -> Bool) (st : WorkQueueState) :
    QueueAction -> WorkQueueState
  | .gpuClaim batch =>
    let nextFront := min (st.front + batch) st.back
    let take := nextFront - st.front
    let segOk := checkRangeBool gpuOk st.front take
    { totalJobs := st.totalJobs
      front := nextFront
      back := st.back
      verifiedCount := st.verifiedCount + take
      allOk := st.allOk && segOk }
  | .cpuSteal batch =>
    let avail := st.back - st.front
    let take := min batch avail
    let nextBack := st.back - take
    let segOk := checkRangeBool cpuOk nextBack take
    { totalJobs := st.totalJobs
      front := st.front
      back := nextBack
      verifiedCount := st.verifiedCount + take
      allOk := st.allOk && segOk }

/-- Executes a trace of GPU front-claims and CPU back-steals. -/
def runWorkQueue (gpuOk cpuOk : Nat -> Bool) (st : WorkQueueState) :
    List QueueAction -> WorkQueueState
  | [] => st
  | a :: as => runWorkQueue gpuOk cpuOk (stepWorkQueue gpuOk cpuOk st a) as

/-- Persistent work-queue invariant across arbitrary GPU front / CPU back interleavings. -/
def WorkQueueInv (isValid : Nat -> Bool) (st : WorkQueueState) : Prop :=
  st.front ≤ st.back ∧
  st.back ≤ st.totalJobs ∧
  st.verifiedCount = st.front + (st.totalJobs - st.back) ∧
  (st.allOk = true ↔
    (∀ i, i < st.front -> isValid i = true) ∧
    (∀ i, st.back ≤ i -> i < st.totalJobs -> isValid i = true))

private theorem stepWorkQueue_preserves_inv {gpuOk cpuOk isValid : Nat -> Bool}
    (hgpu : ∀ i, gpuOk i = isValid i) (hcpu : ∀ i, cpuOk i = isValid i)
    {st : WorkQueueState} (hinv : WorkQueueInv isValid st) (act : QueueAction) :
    WorkQueueInv isValid (stepWorkQueue gpuOk cpuOk st act) := by
  rcases hinv with ⟨hfb, hbt, hcnt, hok⟩
  cases act with
  | gpuClaim batch =>
    unfold stepWorkQueue
    dsimp only
    let nf := min (st.front + batch) st.back
    have hnf_ge : st.front ≤ nf := Nat.le_min.mpr ⟨Nat.le_add_right _ _, hfb⟩
    have hnf_le : nf ≤ st.back := Nat.min_le_right _ _
    have htake : st.front + (nf - st.front) = nf := Nat.add_sub_of_le hnf_ge
    refine ⟨hnf_le, hbt, by dsimp [nf]; omega, ?_⟩
    rw [Bool.and_eq_true, hok, checkRangeBool_iff]
    constructor
    · rintro ⟨⟨hf, hb⟩, hseg⟩
      refine ⟨fun i hi => ?_, hb⟩
      by_cases hlt : i < st.front
      · exact hf i hlt
      · have hlo : st.front ≤ i := Nat.le_of_not_lt hlt
        have hhi : i < st.front + (nf - st.front) := by rw [htake]; exact hi
        rw [← hgpu i]
        exact hseg i hlo hhi
    · rintro ⟨hf, hb⟩
      refine ⟨⟨fun i hi => hf i (Nat.lt_of_lt_of_le hi hnf_ge), hb⟩, ?_⟩
      intro j hlo hhi
      rw [hgpu j]
      exact hf j (by rw [htake] at hhi; exact hhi)
  | cpuSteal batch =>
    unfold stepWorkQueue
    dsimp only
    let take := min batch (st.back - st.front)
    let nb := st.back - take
    have htake_le : take ≤ st.back - st.front := Nat.min_le_right _ _
    have hfb' : st.front ≤ nb := by dsimp [nb]; omega
    have hnb_le : nb ≤ st.back := Nat.sub_le _ _
    have hnb_add : nb + take = st.back := by dsimp [nb]; omega
    refine ⟨hfb', Nat.le_trans hnb_le hbt, by dsimp [take, nb]; omega, ?_⟩
    rw [Bool.and_eq_true, hok, checkRangeBool_iff]
    constructor
    · rintro ⟨⟨hf, hb⟩, hseg⟩
      refine ⟨hf, fun i hlo hhi => ?_⟩
      by_cases hlt : i < st.back
      · rw [← hcpu i]
        exact hseg i hlo (by rw [hnb_add]; exact hlt)
      · exact hb i (Nat.le_of_not_lt hlt) hhi
    · rintro ⟨hf, hb⟩
      refine ⟨⟨hf, fun i hlo hhi => hb i (Nat.le_trans hnb_le hlo) hhi⟩, ?_⟩
      intro j hlo hhi
      rw [hcpu j]
      exact hb j hlo (Nat.lt_of_lt_of_le (by rw [hnb_add] at hhi; exact hhi) hbt)

private theorem runWorkQueue_preserves_inv {gpuOk cpuOk isValid : Nat -> Bool}
    (hgpu : ∀ i, gpuOk i = isValid i) (hcpu : ∀ i, cpuOk i = isValid i)
    {st : WorkQueueState} (hinv : WorkQueueInv isValid st) (acts : List QueueAction) :
    WorkQueueInv isValid (runWorkQueue gpuOk cpuOk st acts) := by
  induction acts generalizing st with
  | nil => exact hinv
  | cons a as ih =>
    exact ih (stepWorkQueue_preserves_inv hgpu hcpu hinv a)

private theorem runWorkQueue_totalJobs (gpuOk cpuOk : Nat -> Bool)
    (st : WorkQueueState) (acts : List QueueAction) :
    (runWorkQueue gpuOk cpuOk st acts).totalJobs = st.totalJobs := by
  induction acts generalizing st with
  | nil => rfl
  | cons a as ih =>
    unfold runWorkQueue
    rw [ih]
    cases a <;> rfl

/-- **Theorem (`twoEndedWorkStealing_sound`)**:
    When GPU workers consume from `front` upward and CPU workers steal from `back` downward
    along any `QueueAction` schedule until `front ≥ back`, every job in `[0, M)` has been
    verified exactly once and `allOk = true ↔ ∀ i < M, isValid i = true`. -/
theorem twoEndedWorkStealing_sound
    (gpuOk cpuOk isValid : Nat -> Bool) (m : Nat) (sched : List QueueAction)
    (hgpu : ∀ i, gpuOk i = isValid i)
    (hcpu : ∀ i, cpuOk i = isValid i) :
    let fin := runWorkQueue gpuOk cpuOk (WorkQueueState.init m) sched
    fin.front ≤ fin.back ∧
    fin.verifiedCount = fin.front + (m - fin.back) ∧
    (fin.front ≥ fin.back ->
      fin.front = fin.back ∧
      fin.verifiedCount = m ∧
      (fin.allOk = true ↔ ∀ i < m, isValid i = true)) := by
  have hinit : WorkQueueInv isValid (WorkQueueState.init m) := by
    refine ⟨Nat.zero_le m, Nat.le_refl m, by simp [WorkQueueState.init], ?_⟩
    simp [WorkQueueState.init]
    intro i hlo hlt
    omega
  have hinv := runWorkQueue_preserves_inv hgpu hcpu hinit sched
  have htot : (runWorkQueue gpuOk cpuOk (WorkQueueState.init m) sched).totalJobs = m :=
    runWorkQueue_totalJobs gpuOk cpuOk (WorkQueueState.init m) sched
  rcases hinv with ⟨hfb, hbm, hcnt, hok⟩
  rw [htot] at hbm hcnt hok
  refine ⟨hfb, hcnt, fun hdone => ?_⟩
  have heq : (runWorkQueue gpuOk cpuOk (WorkQueueState.init m) sched).front =
      (runWorkQueue gpuOk cpuOk (WorkQueueState.init m) sched).back := Nat.le_antisymm hfb hdone
  refine ⟨heq, by omega, ?_⟩
  rw [hok]
  constructor
  · rintro ⟨hf, hb⟩ i hi
    by_cases hlt : i < (runWorkQueue gpuOk cpuOk (WorkQueueState.init m) sched).front
    · exact hf i hlt
    · exact hb i (by rw [← heq]; exact Nat.le_of_not_lt hlt) hi
  · intro hall
    exact ⟨fun i hi => hall i (Nat.lt_of_lt_of_le hi (Nat.le_trans hfb hbm)),
           fun i _ hi => hall i hi⟩


/-! ### 3. Wider Exact WGSL Reductions (Base-`2^32` Limbs, `String` Words, `k`-Field Eta) -/

/-- Little-endian base-`2^32` value of a limb list. -/
def evalLimbs : List UInt32 -> Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 32 * evalLimbs ws

/-- Strips redundant trailing zero limbs (`0` at the most-significant end) so `0 ↦ []`. -/
def normalizeLimbs : List UInt32 -> List UInt32
  | [] => []
  | w :: ws =>
    match normalizeLimbs ws with
    | [] => if w == 0 then [] else [w]
    | ys => w :: ys

/-- Canonical limb-list invariant: no redundant most-significant zero limbs. -/
def WellFormedLimbs (ws : List UInt32) : Prop :=
  normalizeLimbs ws = ws

theorem evalLimbs_normalize (ws : List UInt32) :
    evalLimbs (normalizeLimbs ws) = evalLimbs ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    unfold normalizeLimbs
    cases hnorm : normalizeLimbs ws with
    | nil =>
      rw [hnorm] at ih
      dsimp only
      by_cases hw : w == 0
      · simp only [hw, ↓reduceIte, evalLimbs]
        have hw0 : w.toNat = 0 := by rw [beq_iff_eq.mp hw]; rfl
        rw [hw0, ← ih, evalLimbs]
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, evalLimbs]
        rw [← ih, evalLimbs]
    | cons y ys =>
      rw [hnorm] at ih
      change w.toNat + 2 ^ 32 * evalLimbs (y :: ys) = w.toNat + 2 ^ 32 * evalLimbs ws
      rw [ih]

theorem normalizeLimbs_idempotent (ws : List UInt32) :
    normalizeLimbs (normalizeLimbs ws) = normalizeLimbs ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : normalizeLimbs (w :: ws) =
        match normalizeLimbs ws with
        | [] => if w == 0 then [] else [w]
        | ys => w :: ys := rfl
    rw [hstep]
    cases hnorm : normalizeLimbs ws with
    | nil =>
      by_cases hw : (w == 0) = true
      · simp only [hw, ↓reduceIte]; rfl
      · simp [normalizeLimbs, hw]
    | cons y ys =>
      rw [hnorm] at ih
      dsimp only
      have houter : normalizeLimbs (w :: y :: ys) =
          match normalizeLimbs (y :: ys) with
          | [] => if w == 0 then [] else [w]
          | zs => w :: zs := rfl
      rw [houter, ih]

theorem wellFormed_normalize (ws : List UInt32) :
    WellFormedLimbs (normalizeLimbs ws) :=
  normalizeLimbs_idempotent ws

private theorem ui32_eq_of_toNat {a b : UInt32} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b; congr; exact BitVec.eq_of_toNat_eq h

private theorem limb_zero_iff_toNat_zero (w : UInt32) :
    w = 0 ↔ w.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact ui32_eq_of_toNat h

private theorem limb_decomp_eq {a b q1 q2 M : Nat} (hM : 0 < M)
    (ha : a < M) (hb : b < M) (heq : a + M * q1 = b + M * q2) :
    a = b ∧ q1 = q2 := by
  have h1 : a + M * q1 = a + q1 * M := by rw [Nat.mul_comm]
  have h2 : b + M * q2 = b + q2 * M := by rw [Nat.mul_comm]
  have heq' : a + q1 * M = b + q2 * M := by rw [← h1, ← h2, heq]
  have hdiv : (a + q1 * M) / M = (b + q2 * M) / M := congrArg (· / M) heq'
  rw [Nat.add_mul_div_right _ _ hM, Nat.add_mul_div_right _ _ hM] at hdiv
  rw [Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.zero_add, Nat.zero_add] at hdiv
  refine ⟨?_, hdiv⟩
  rw [hdiv] at heq
  exact Nat.add_right_cancel heq

theorem evalLimbs_eq_zero_iff {ws : List UInt32} (hwf : WellFormedLimbs ws) :
    evalLimbs ws = 0 ↔ ws = [] := by
  constructor
  · intro hev
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      unfold evalLimbs at hev
      have hpow : 0 < 2 ^ 32 := by decide
      have hw0 : w.toNat = 0 := by
        by_cases hw : w.toNat = 0
        · exact hw
        · exfalso
          have hpos : 0 < w.toNat + 2 ^ 32 * evalLimbs ws := by omega
          omega
      have hws0 : evalLimbs ws = 0 := by
        rw [hw0, Nat.zero_add] at hev
        rcases Nat.mul_eq_zero.mp hev with hz | hz
        · have hne : 2 ^ 32 ≠ 0 := by decide
          exact absurd hz hne
        · exact hz
      have hwz : w = 0 := (limb_zero_iff_toNat_zero w).mpr hw0
      unfold WellFormedLimbs normalizeLimbs at hwf
      have hnorm_ws : normalizeLimbs ws = [] := by
        have hen := evalLimbs_normalize ws
        rw [hws0] at hen
        cases hn : normalizeLimbs ws with
        | nil => rfl
        | cons z zs =>
          exfalso
          have hwf' : normalizeLimbs (w :: ws) = w :: ws := hwf
          unfold normalizeLimbs at hwf'
          rw [hn] at hwf'
          injection hwf' with _ hws_eq
          have hwf_ws : WellFormedLimbs ws := hn.trans hws_eq
          have := ih hwf_ws hws0
          rw [this] at hn
          simp [normalizeLimbs] at hn
      rw [hnorm_ws] at hwf
      have hbeq : (w == 0) = true := beq_iff_eq.mpr hwz
      simp [hbeq] at hwf
  · intro h; rw [h]; rfl

private theorem wellFormed_tail {w : UInt32} {ws : List UInt32}
    (hwf : WellFormedLimbs (w :: ws)) : WellFormedLimbs ws := by
  unfold WellFormedLimbs at hwf ⊢
  unfold normalizeLimbs at hwf
  cases hnorm : normalizeLimbs ws with
  | nil =>
    rw [hnorm] at hwf
    dsimp only at hwf
    by_cases hw : w == 0
    · simp [hw] at hwf
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, List.cons.injEq] at hwf
      rcases hwf with ⟨_, hnil⟩
      rw [← hnil] at hnorm
      rw [← hnil]
  | cons y ys =>
    rw [hnorm] at hwf
    dsimp only at hwf
    injection hwf with _ htail

theorem evalLimbs_injective {xs ys : List UInt32}
    (hxs : WellFormedLimbs xs) (hys : WellFormedLimbs ys)
    (heq : evalLimbs xs = evalLimbs ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    have hy0 : evalLimbs ys = 0 := heq.symm
    exact ((evalLimbs_eq_zero_iff hys).mp hy0).symm
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hx0 : evalLimbs (x :: xs) = 0 := heq
      exact (evalLimbs_eq_zero_iff hxs).mp hx0
    | cons y ys =>
      unfold evalLimbs at heq
      obtain ⟨hxyNat, htailEq⟩ := limb_decomp_eq (by decide) x.toNat_lt_size y.toNat_lt_size heq
      have hxy : x = y := ui32_eq_of_toNat hxyNat
      have htail := ih (wellFormed_tail hxs) (wellFormed_tail hys) htailEq
      rw [hxy, htail]

private theorem ui32_add_carry_iff_p4 (x y : UInt32) :
    ((x + y < x) ↔ 2 ^ 32 ≤ x.toNat + y.toNat) ∧
    ((if x + y < x then 2 ^ 32 else 0) + (x + y).toNat = x.toNat + y.toNat) := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
  have hy : y.toNat < 2 ^ 32 := y.toNat_lt_size
  have hadd : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := UInt32.toNat_add x y
  change ((x + y).toNat < x.toNat ↔ 2 ^ 32 ≤ x.toNat + y.toNat) ∧ _
  by_cases hge : 2 ^ 32 ≤ x.toNat + y.toNat
  · have hmod : (x.toNat + y.toNat) % 2 ^ 32 = x.toNat + y.toNat - 2 ^ 32 := by omega
    have hlt : (x + y).toNat < x.toNat := by rw [hadd, hmod]; omega
    constructor
    · exact ⟨fun _ => hge, fun _ => hlt⟩
    · change (if (x + y).toNat < x.toNat then 2 ^ 32 else 0) + (x + y).toNat = x.toNat + y.toNat
      simp only [hlt, ↓reduceIte]
      rw [hadd, hmod]
      omega
  · have hlt_sum : x.toNat + y.toNat < 2 ^ 32 := by omega
    have hmod : (x.toNat + y.toNat) % 2 ^ 32 = x.toNat + y.toNat := Nat.mod_eq_of_lt hlt_sum
    have hnlt : ¬ ((x + y).toNat < x.toNat) := by rw [hadd, hmod]; omega
    constructor
    · exact ⟨fun h => absurd h hnlt, fun h => absurd h hge⟩
    · change (if (x + y).toNat < x.toNat then 2 ^ 32 else 0) + (x + y).toNat = x.toNat + y.toNat
      simp only [hnlt, ↓reduceIte]
      rw [hadd, hmod, Nat.zero_add]

private def add3Limb (x y c : UInt32) : UInt32 × UInt32 :=
  let s1 := x + y
  let c1 : UInt32 := if s1 < x then 1 else 0
  let s2 := s1 + c
  let c2 : UInt32 := if s2 < s1 then 1 else 0
  (s2, c1 + c2)

private theorem add3Limb_step_arith {x y c s1 s2 c1 c2 : Nat}
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hc : c ≤ 1)
    (_hs1 : s1 < 2 ^ 32) (hs2 : s2 < 2 ^ 32)
    (_hc1_bound : c1 ≤ 1) (_hc2_bound : c2 ≤ 1)
    (h1 : c1 * 2 ^ 32 + s1 = x + y)
    (h2 : c2 * 2 ^ 32 + s2 = s1 + c) :
    s2 + 2 ^ 32 * (c1 + c2) = x + y + c ∧ c1 + c2 ≤ 1 := by
  have hsum : s2 + 2 ^ 32 * (c1 + c2) = x + y + c := by
    calc s2 + 2 ^ 32 * (c1 + c2)
        = (c2 * 2 ^ 32 + s2) + c1 * 2 ^ 32 := by
          rw [Nat.mul_add, Nat.mul_comm (2 ^ 32) c1, Nat.mul_comm (2 ^ 32) c2]; omega
      _ = (s1 + c) + c1 * 2 ^ 32 := by rw [h2]
      _ = (c1 * 2 ^ 32 + s1) + c := by omega
      _ = x + y + c := by rw [h1]
  have hle : c1 + c2 ≤ 1 := by
    by_cases hok : c1 + c2 ≤ 1
    · exact hok
    · exfalso
      have hge2 : 2 ≤ c1 + c2 := Nat.le_of_not_lt (fun h => hok (Nat.lt_succ_iff.mp h))
      have hmul : 2 * 2 ^ 32 ≤ 2 ^ 32 * (c1 + c2) := by
        rw [Nat.mul_comm (2 ^ 32)]; exact Nat.mul_le_mul_right _ hge2
      have hlo : 2 * 2 ^ 32 ≤ x + y + c := by
        rw [← hsum]; exact Nat.le_trans hmul (Nat.le_add_left _ _)
      have hmax1 : x ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hx
      have hmax2 : y ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hy
      have htop : x + y + c ≤ (2 ^ 32 - 1) + (2 ^ 32 - 1) + 1 := by omega
      have hlt_pow : (2 ^ 32 - 1) + (2 ^ 32 - 1) + 1 < 2 * 2 ^ 32 := by decide
      exact absurd (Nat.le_trans hlo htop) (Nat.not_le_of_gt hlt_pow)
  exact ⟨hsum, hle⟩

private theorem add3Limb_correct (x y c : UInt32) (hc : c.toNat ≤ 1) :
    let res := add3Limb x y c
    res.1.toNat + 2 ^ 32 * res.2.toNat = x.toNat + y.toNat + c.toNat ∧ res.2.toNat ≤ 1 := by
  unfold add3Limb
  dsimp only
  have h1 := (ui32_add_carry_iff_p4 x y).2
  have h2 := (ui32_add_carry_iff_p4 (x + y) c).2
  have hc1n : (if x + y < x then (1 : UInt32) else 0).toNat ≤ 1 := by
    split <;> decide
  have hc2n : (if (x + y) + c < x + y then (1 : UInt32) else 0).toNat ≤ 1 := by
    split <;> decide
  have h1' : (if x + y < x then (1 : UInt32) else 0).toNat * 2 ^ 32 + (x + y).toNat =
      x.toNat + y.toNat := by
    have ht : (if x + y < x then (1 : UInt32) else 0).toNat * 2 ^ 32 =
        if x + y < x then 2 ^ 32 else 0 := by
      split <;> simp
    rw [ht]; exact h1
  have h2' : (if (x + y) + c < x + y then (1 : UInt32) else 0).toNat * 2 ^ 32 + ((x + y) + c).toNat =
      (x + y).toNat + c.toNat := by
    have ht : (if (x + y) + c < x + y then (1 : UInt32) else 0).toNat * 2 ^ 32 =
        if (x + y) + c < x + y then 2 ^ 32 else 0 := by
      split <;> simp
    rw [ht]; exact h2
  have hstep := add3Limb_step_arith x.toNat_lt_size y.toNat_lt_size hc
    (x + y).toNat_lt_size ((x + y) + c).toNat_lt_size hc1n hc2n h1' h2'
  have hcSum : ((if x + y < x then (1 : UInt32) else 0) +
      (if (x + y) + c < x + y then (1 : UInt32) else 0)).toNat =
      (if x + y < x then (1 : UInt32) else 0).toNat +
      (if (x + y) + c < x + y then (1 : UInt32) else 0).toNat := by
    rw [UInt32.toNat_add]
    have hlt_sum : (if x + y < x then (1 : UInt32) else 0).toNat +
        (if (x + y) + c < x + y then (1 : UInt32) else 0).toNat ≤ 2 := Nat.add_le_add hc1n hc2n
    have h2lt : 2 < 2 ^ 32 := by decide
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hlt_sum h2lt)
  rw [hcSum]
  exact hstep

/-- Carry-propagating little-endian multi-limb natural number addition. -/
def addLimbsRaw : List UInt32 -> List UInt32 -> UInt32 -> List UInt32
  | [], [], c => if c == 0 then [] else [c]
  | x :: xs, [], c =>
    let r := add3Limb x 0 c
    r.1 :: addLimbsRaw xs [] r.2
  | [], y :: ys, c =>
    let r := add3Limb 0 y c
    r.1 :: addLimbsRaw [] ys r.2
  | x :: xs, y :: ys, c =>
    let r := add3Limb x y c
    r.1 :: addLimbsRaw xs ys r.2

/-- Canonical multi-limb addition returning normalized little-endian `UInt32` limbs. -/
def multiLimbNatAdd (xs ys : List UInt32) : List UInt32 :=
  normalizeLimbs (addLimbsRaw xs ys 0)

private theorem addLimbsRaw_eval (xs ys : List UInt32) (c : UInt32) (hc : c.toNat ≤ 1) :
    evalLimbs (addLimbsRaw xs ys c) = evalLimbs xs + evalLimbs ys + c.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil =>
      unfold addLimbsRaw evalLimbs
      by_cases hcz : c == 0
      · simp only [hcz, ↓reduceIte]
        have hc0 : c.toNat = 0 := by rw [beq_iff_eq.mp hcz]; rfl
        rw [hc0]
      · simp only [hcz, Bool.false_eq_true, ↓reduceIte, evalLimbs]
        simp
    | cons y ys ihy =>
      unfold addLimbsRaw evalLimbs
      have hstep := add3Limb_correct 0 y c hc
      dsimp only at hstep ⊢
      rw [ihy (add3Limb 0 y c).2 hstep.2]
      have hz : (0 : UInt32).toNat = 0 := rfl
      rw [hz, Nat.zero_add] at hstep
      have hz0 : evalLimbs [] = 0 := rfl
      rw [hz0, Nat.zero_add]
      calc (add3Limb 0 y c).1.toNat + 2 ^ 32 * (evalLimbs ys + (add3Limb 0 y c).2.toNat)
          = ((add3Limb 0 y c).1.toNat + 2 ^ 32 * (add3Limb 0 y c).2.toNat) + 2 ^ 32 * evalLimbs ys := by
            rw [Nat.mul_add]; omega
        _ = (y.toNat + c.toNat) + 2 ^ 32 * evalLimbs ys := by rw [hstep.1]
        _ = 0 + (y.toNat + 2 ^ 32 * evalLimbs ys) + c.toNat := by omega
  | cons x xs ihx =>
    cases ys with
    | nil =>
      unfold addLimbsRaw evalLimbs
      have hstep := add3Limb_correct x 0 c hc
      dsimp only at hstep ⊢
      rw [ihx [] (add3Limb x 0 c).2 hstep.2]
      have hz : (0 : UInt32).toNat = 0 := rfl
      rw [hz, Nat.add_zero] at hstep
      calc (add3Limb x 0 c).1.toNat + 2 ^ 32 * (evalLimbs xs + 0 + (add3Limb x 0 c).2.toNat)
          = ((add3Limb x 0 c).1.toNat + 2 ^ 32 * (add3Limb x 0 c).2.toNat) + 2 ^ 32 * evalLimbs xs := by
            rw [Nat.add_zero, Nat.mul_add]; omega
        _ = (x.toNat + c.toNat) + 2 ^ 32 * evalLimbs xs := by rw [hstep.1]
        _ = x.toNat + 2 ^ 32 * evalLimbs xs + 0 + c.toNat := by omega
    | cons y ys =>
      unfold addLimbsRaw evalLimbs
      have hstep := add3Limb_correct x y c hc
      dsimp only at hstep ⊢
      rw [ihx ys (add3Limb x y c).2 hstep.2]
      calc (add3Limb x y c).1.toNat + 2 ^ 32 * (evalLimbs xs + evalLimbs ys + (add3Limb x y c).2.toNat)
          = ((add3Limb x y c).1.toNat + 2 ^ 32 * (add3Limb x y c).2.toNat) +
              (2 ^ 32 * evalLimbs xs + 2 ^ 32 * evalLimbs ys) := by
            rw [Nat.mul_add, Nat.mul_add]; omega
        _ = (x.toNat + y.toNat + c.toNat) + (2 ^ 32 * evalLimbs xs + 2 ^ 32 * evalLimbs ys) := by
            rw [hstep.1]
        _ = (x.toNat + 2 ^ 32 * evalLimbs xs) + (y.toNat + 2 ^ 32 * evalLimbs ys) + c.toNat := by
            omega

/-- **Theorem (`multiLimbNatAdd_correct`)**:
    `multiLimbNatAdd xs ys` evaluates identically to `evalLimbs xs + evalLimbs ys` and
    produces `WellFormedLimbs`. -/
theorem multiLimbNatAdd_correct (xs ys : List UInt32) :
    evalLimbs (multiLimbNatAdd xs ys) = evalLimbs xs + evalLimbs ys ∧
    WellFormedLimbs (multiLimbNatAdd xs ys) := by
  unfold multiLimbNatAdd
  refine ⟨?_, wellFormed_normalize _⟩
  rw [evalLimbs_normalize, addLimbsRaw_eval xs ys 0 (by decide)]
  simp

/-- Bottom-up lexicographic comparison of little-endian limb lists. -/
def cmpLimbs : List UInt32 -> List UInt32 -> Ordering
  | [], [] => .eq
  | [], y :: ys =>
    match cmpLimbs [] ys with
    | .eq => if y == 0 then .eq else .lt
    | o => o
  | x :: xs, [] =>
    match cmpLimbs xs [] with
    | .eq => if x == 0 then .eq else .gt
    | o => o
  | x :: xs, y :: ys =>
    match cmpLimbs xs ys with
    | .eq => compare x.toNat y.toNat
    | o => o

private theorem limb_lt_mul_shift {a b x y M : Nat} (_hM : 0 < M)
    (ha : a < M) (hlt : x < y) : a + M * x < b + M * y := by
  have hy : x + 1 ≤ y := hlt
  have hm : M * (x + 1) ≤ M * y := Nat.mul_le_mul_left M hy
  have h1 : a + M * x < M * (x + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (M * x) M]
    exact Nat.add_lt_add_right ha (M * x)
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans hm (Nat.le_add_left _ _))

private theorem compare_nat_eq_left {x y : Nat} (h : compare x y = .eq) : x = y := by
  unfold compare instOrdNat compareOfLessAndEq at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

private theorem compare_nat_lt_left {x y : Nat} (h : compare x y = .lt) : x < y := by
  unfold compare instOrdNat compareOfLessAndEq at h
  dsimp only at h
  split at h
  · assumption
  · split at h <;> cases h

private theorem compare_nat_gt_left {x y : Nat} (h : compare x y = .gt) : y < x := by
  unfold compare instOrdNat compareOfLessAndEq at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · omega

private theorem cmpLimbs_eq_compare (xs ys : List UInt32) :
    cmpLimbs xs ys = compare (evalLimbs xs) (evalLimbs ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [cmpLimbs, evalLimbs, compare, compareOfLessAndEq]
    | cons y ys ihy =>
      unfold cmpLimbs evalLimbs
      rw [ihy]
      have h0 : evalLimbs [] = 0 := rfl
      rw [h0]
      cases hcmp : compare 0 (evalLimbs ys) with
      | eq =>
        have hy0 : 0 = evalLimbs ys := compare_nat_eq_left hcmp
        rw [← hy0, Nat.mul_zero, Nat.add_zero]
        by_cases hy : y == 0
        · simp only [hy, ↓reduceIte]
          have hyn : y.toNat = 0 := by rw [beq_iff_eq.mp hy]; rfl
          rw [hyn]; rfl
        · simp only [hy, Bool.false_eq_true, ↓reduceIte]
          have hyn : y.toNat ≠ 0 := fun hz => hy (beq_iff_eq.mpr ((limb_zero_iff_toNat_zero y).mpr hz))
          have hpos : 0 < y.toNat := Nat.pos_of_ne_zero hyn
          symm
          simp [compare, compareOfLessAndEq, hpos]
      | lt =>
        have hlt : 0 < evalLimbs ys := compare_nat_lt_left hcmp
        have hpos : 0 < y.toNat + 2 ^ 32 * evalLimbs ys := by
          have : 0 < 2 ^ 32 := by decide
          have : 0 < 2 ^ 32 * evalLimbs ys := Nat.mul_pos this hlt
          omega
        symm
        simp [compare, compareOfLessAndEq, hpos]
      | gt =>
        have hgt : evalLimbs ys < 0 := compare_nat_gt_left hcmp
        omega
  | cons x xs ihx =>
    cases ys with
    | nil =>
      unfold cmpLimbs evalLimbs
      rw [ihx []]
      have h0 : evalLimbs [] = 0 := rfl
      rw [h0]
      cases hcmp : compare (evalLimbs xs) 0 with
      | eq =>
        have hx0 : evalLimbs xs = 0 := compare_nat_eq_left hcmp
        rw [hx0, Nat.mul_zero, Nat.add_zero]
        by_cases hx : x == 0
        · simp only [hx, ↓reduceIte]
          have hxn : x.toNat = 0 := by rw [beq_iff_eq.mp hx]; rfl
          rw [hxn]
          simp [compare, compareOfLessAndEq]
        · simp only [hx, Bool.false_eq_true, ↓reduceIte]
          have hxn : x.toNat ≠ 0 := fun hz => hx (beq_iff_eq.mpr ((limb_zero_iff_toNat_zero x).mpr hz))
          have hpos : 0 < x.toNat := Nat.pos_of_ne_zero hxn
          symm
          unfold compare instOrdNat compareOfLessAndEq
          dsimp only
          repeat (first | rfl | omega | split)
      | lt =>
        have hlt : evalLimbs xs < 0 := compare_nat_lt_left hcmp
        omega
      | gt =>
        have hgt : 0 < evalLimbs xs := compare_nat_gt_left hcmp
        have hpos : 0 < x.toNat + 2 ^ 32 * evalLimbs xs := by
          have : 0 < 2 ^ 32 := by decide
          have : 0 < 2 ^ 32 * evalLimbs xs := Nat.mul_pos this hgt
          omega
        symm
        unfold compare instOrdNat compareOfLessAndEq
        dsimp only
        repeat (first | rfl | omega | split)
    | cons y ys =>
      unfold cmpLimbs evalLimbs
      rw [ihx ys]
      cases hcmp : compare (evalLimbs xs) (evalLimbs ys) with
      | eq =>
        have heq : evalLimbs xs = evalLimbs ys := compare_nat_eq_left hcmp
        rw [heq]
        unfold compare instOrdNat compareOfLessAndEq
        dsimp only
        split
        · split <;> first | rfl | omega
        · split
          · split
            · omega
            · split <;> first | rfl | omega
          · split
            · omega
            · split <;> first | rfl | omega
      | lt =>
        have hlt : evalLimbs xs < evalLimbs ys := compare_nat_lt_left hcmp
        have hlt' : x.toNat + 2 ^ 32 * evalLimbs xs < y.toNat + 2 ^ 32 * evalLimbs ys :=
          limb_lt_mul_shift (by decide) x.toNat_lt_size hlt
        symm
        simp [compare, compareOfLessAndEq, hlt']
      | gt =>
        have hgt : evalLimbs ys < evalLimbs xs := compare_nat_gt_left hcmp
        have hgt' : y.toNat + 2 ^ 32 * evalLimbs ys < x.toNat + 2 ^ 32 * evalLimbs xs :=
          limb_lt_mul_shift (by decide) y.toNat_lt_size hgt
        symm
        simp [compare, compareOfLessAndEq, Nat.not_lt_of_gt hgt', Ne.symm (Nat.ne_of_lt hgt')]

/-- Multi-limb natural number equality test. -/
def multiLimbNatBeq (xs ys : List UInt32) : Bool :=
  cmpLimbs xs ys == .eq

/-- Multi-limb natural number `≤` comparison. -/
def multiLimbNatBle (xs ys : List UInt32) : Bool :=
  cmpLimbs xs ys != .gt

/-- **Theorem (`multiLimbNatBeq_correct`)**:
    `multiLimbNatBeq xs ys = true ↔ evalLimbs xs = evalLimbs ys` (and for `WellFormedLimbs`,
    matches structural equality `xs == ys`). -/
theorem multiLimbNatBeq_correct (xs ys : List UInt32) :
    (multiLimbNatBeq xs ys = true ↔ evalLimbs xs = evalLimbs ys) ∧
    (WellFormedLimbs xs -> WellFormedLimbs ys ->
      ((xs == ys) = true ↔ evalLimbs xs = evalLimbs ys)) := by
  refine ⟨?_, ?_⟩
  · unfold multiLimbNatBeq
    rw [cmpLimbs_eq_compare]
    unfold compare instOrdNat compareOfLessAndEq
    by_cases h1 : evalLimbs xs < evalLimbs ys
    · simp [h1, Nat.ne_of_lt h1]
    · by_cases h2 : evalLimbs xs = evalLimbs ys
      · simp [h2]
      · simp [h1, h2]
  · intro hxs hys
    rw [beq_iff_eq]
    exact ⟨fun h => by rw [h], fun h => evalLimbs_injective hxs hys h⟩

/-- **Theorem (`multiLimbNatBle_correct`)**:
    `multiLimbNatBle xs ys = true ↔ evalLimbs xs ≤ evalLimbs ys`. -/
theorem multiLimbNatBle_correct (xs ys : List UInt32) :
    multiLimbNatBle xs ys = true ↔ evalLimbs xs ≤ evalLimbs ys := by
  unfold multiLimbNatBle
  rw [cmpLimbs_eq_compare]
  unfold compare instOrdNat compareOfLessAndEq
  by_cases h1 : evalLimbs xs < evalLimbs ys
  · simp [h1, Nat.le_of_lt h1]
  · by_cases h2 : evalLimbs xs = evalLimbs ys
    · simp [h2]
    · have hgt : evalLimbs ys < evalLimbs xs := by omega
      simp [h1, h2, Nat.not_le_of_gt hgt]

private def sub3Limb (x y b : UInt32) : UInt32 × UInt32 :=
  let b1 : UInt32 := if x < y then 1 else 0
  let d1 := x - y
  let b2 : UInt32 := if d1 < b then 1 else 0
  (d1 - b, b1 + b2)

private theorem ui32_sub_borrow_iff (x y : UInt32) :
    (x - y).toNat + y.toNat = x.toNat + if x < y then 2 ^ 32 else 0 := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
  have hy : y.toNat < 2 ^ 32 := y.toNat_lt_size
  have hsub : (x - y).toNat = (2 ^ 32 - y.toNat + x.toNat) % 2 ^ 32 := UInt32.toNat_sub x y
  change (x - y).toNat + y.toNat = x.toNat + if x.toNat < y.toNat then 2 ^ 32 else 0
  by_cases hlt : x.toNat < y.toNat
  · simp only [hlt, ↓reduceIte]
    have hlt2 : 2 ^ 32 - y.toNat + x.toNat < 2 ^ 32 := by omega
    rw [hsub, Nat.mod_eq_of_lt hlt2]
    omega
  · simp only [hlt, ↓reduceIte]
    have hge : y.toNat ≤ x.toNat := Nat.le_of_not_lt hlt
    have hmod : (2 ^ 32 - y.toNat + x.toNat) % 2 ^ 32 = x.toNat - y.toNat := by
      have heq : 2 ^ 32 - y.toNat + x.toNat = (x.toNat - y.toNat) + 1 * 2 ^ 32 := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, hmod]
    omega

private theorem sub3Limb_step_arith {x y b d1 d b1 b2 : Nat}
    (_hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hb : b ≤ 1)
    (hd : d < 2 ^ 32) (_hb1_bound : b1 ≤ 1) (_hb2_bound : b2 ≤ 1)
    (h1 : d1 + y = x + b1 * 2 ^ 32)
    (h2 : d + b = d1 + b2 * 2 ^ 32) :
    d + y + b = x + 2 ^ 32 * (b1 + b2) ∧ b1 + b2 ≤ 1 := by
  have hsum : d + y + b = x + 2 ^ 32 * (b1 + b2) := by
    calc d + y + b
        = (d + b) + y := by omega
      _ = (d1 + b2 * 2 ^ 32) + y := by rw [h2]
      _ = (d1 + y) + b2 * 2 ^ 32 := by omega
      _ = (x + b1 * 2 ^ 32) + b2 * 2 ^ 32 := by rw [h1]
      _ = x + 2 ^ 32 * (b1 + b2) := by
          rw [Nat.mul_add, Nat.mul_comm (2 ^ 32) b1, Nat.mul_comm (2 ^ 32) b2]; omega
  have hle : b1 + b2 ≤ 1 := by
    by_cases hok : b1 + b2 ≤ 1
    · exact hok
    · exfalso
      have hge2 : 2 ≤ b1 + b2 := Nat.le_of_not_lt (fun h => hok (Nat.lt_succ_iff.mp h))
      have hmul : 2 * 2 ^ 32 ≤ 2 ^ 32 * (b1 + b2) := by
        rw [Nat.mul_comm (2 ^ 32)]; exact Nat.mul_le_mul_right _ hge2
      have hlo : 2 * 2 ^ 32 ≤ d + y + b := by
        rw [hsum]; exact Nat.le_trans hmul (Nat.le_add_left _ _)
      have htop : d + y + b ≤ (2 ^ 32 - 1) + (2 ^ 32 - 1) + 1 := by omega
      have hlt_pow : (2 ^ 32 - 1) + (2 ^ 32 - 1) + 1 < 2 * 2 ^ 32 := by decide
      exact absurd (Nat.le_trans hlo htop) (Nat.not_le_of_gt hlt_pow)
  exact ⟨hsum, hle⟩

private theorem sub3Limb_correct (x y b : UInt32) (hb : b.toNat ≤ 1) :
    let res := sub3Limb x y b
    res.1.toNat + y.toNat + b.toNat = x.toNat + 2 ^ 32 * res.2.toNat ∧ res.2.toNat ≤ 1 := by
  unfold sub3Limb
  dsimp only
  have h1 := ui32_sub_borrow_iff x y
  have h2 := ui32_sub_borrow_iff (x - y) b
  have hb1n : (if x < y then (1 : UInt32) else 0).toNat ≤ 1 := by split <;> decide
  have hb2n : (if x - y < b then (1 : UInt32) else 0).toNat ≤ 1 := by split <;> decide
  have h1' : (x - y).toNat + y.toNat =
      x.toNat + (if x < y then (1 : UInt32) else 0).toNat * 2 ^ 32 := by
    have ht : (if x < y then (1 : UInt32) else 0).toNat * 2 ^ 32 =
        if x < y then 2 ^ 32 else 0 := by split <;> simp
    rw [ht]; exact h1
  have h2' : ((x - y) - b).toNat + b.toNat =
      (x - y).toNat + (if x - y < b then (1 : UInt32) else 0).toNat * 2 ^ 32 := by
    have ht : (if x - y < b then (1 : UInt32) else 0).toNat * 2 ^ 32 =
        if x - y < b then 2 ^ 32 else 0 := by split <;> simp
    rw [ht]; exact h2
  have hstep := sub3Limb_step_arith x.toNat_lt_size y.toNat_lt_size hb
    ((x - y) - b).toNat_lt_size hb1n hb2n h1' h2'
  have hbSum : ((if x < y then (1 : UInt32) else 0) +
      (if x - y < b then (1 : UInt32) else 0)).toNat =
      (if x < y then (1 : UInt32) else 0).toNat +
      (if x - y < b then (1 : UInt32) else 0).toNat := by
    rw [UInt32.toNat_add]
    have hlt_sum := Nat.add_le_add hb1n hb2n
    have h2lt : 2 < 2 ^ 32 := by decide
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hlt_sum h2lt)
  rw [hbSum]
  exact hstep

/-- Borrow-propagating raw little-endian limb subtraction (valid when minuend ≥ subtrahend). -/
def subLimbsRaw : List UInt32 -> List UInt32 -> UInt32 -> List UInt32
  | [], _, _ => []
  | x :: xs, [], b =>
    let r := sub3Limb x 0 b
    r.1 :: subLimbsRaw xs [] r.2
  | x :: xs, y :: ys, b =>
    let r := sub3Limb x y b
    r.1 :: subLimbsRaw xs ys r.2

/-- Truncating canonical multi-limb natural number subtraction (`0` when `xs < ys`). -/
def multiLimbNatSub (xs ys : List UInt32) : List UInt32 :=
  if multiLimbNatBle ys xs then normalizeLimbs (subLimbsRaw xs ys 0) else []

private theorem sub_borrow_le_tail {d x y xs ys b : Nat}
    (hd : d < 2 ^ 32) (hstep : d + y = x + 2 ^ 32 * b)
    (hle : y + 2 ^ 32 * ys ≤ x + 2 ^ 32 * xs) :
    ys + b ≤ xs := by
  have hmul : 2 ^ 32 * (ys + b) ≤ d + 2 ^ 32 * xs := by
    calc 2 ^ 32 * (ys + b)
        = (y + 2 ^ 32 * ys) + 2 ^ 32 * b - y := by omega
      _ ≤ (x + 2 ^ 32 * xs) + 2 ^ 32 * b - y := by
          have h1 : y + 2 ^ 32 * ys + 2 ^ 32 * b ≤ x + 2 ^ 32 * xs + 2 ^ 32 * b :=
            Nat.add_le_add_right hle _
          omega
      _ = d + 2 ^ 32 * xs := by omega
  by_cases hok : ys + b ≤ xs
  · exact hok
  · exfalso
    have hge : xs + 1 ≤ ys + b := Nat.lt_of_not_le hok
    have h1 : 2 ^ 32 * (xs + 1) ≤ 2 ^ 32 * (ys + b) := Nat.mul_le_mul_left _ hge
    have h2 : d + 2 ^ 32 * xs < 2 ^ 32 * (xs + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (2 ^ 32 * xs) (2 ^ 32)]
      exact Nat.add_lt_add_right hd _
    exact absurd (Nat.le_trans h1 hmul) (Nat.not_le_of_gt h2)

private theorem subLimbsRaw_eval (xs ys : List UInt32) (b : UInt32)
    (hb : b.toNat ≤ 1) (hle : evalLimbs ys + b.toNat ≤ evalLimbs xs) :
    evalLimbs (subLimbsRaw xs ys b) + evalLimbs ys + b.toNat = evalLimbs xs := by
  induction xs generalizing ys b with
  | nil =>
    have hx0 : evalLimbs [] = 0 := rfl
    rw [hx0] at hle
    have hy0 : evalLimbs ys = 0 := by omega
    have hb0 : b.toNat = 0 := by omega
    simp [subLimbsRaw, evalLimbs, hy0, hb0]
  | cons x xs ihx =>
    cases ys with
    | nil =>
      unfold subLimbsRaw evalLimbs
      have hstep := sub3Limb_correct x 0 b hb
      dsimp only at hstep ⊢
      have hyz : (0 : UInt32).toNat = 0 := rfl
      rw [hyz, Nat.add_zero] at hstep
      have hle_tail : evalLimbs [] + (sub3Limb x 0 b).2.toNat ≤ evalLimbs xs := by
        have hx' : evalLimbs [] = 0 := rfl
        rw [hx', Nat.zero_add]
        have hsub : (sub3Limb x 0 b).1.toNat + b.toNat =
            x.toNat + 2 ^ 32 * (sub3Limb x 0 b).2.toNat := hstep.1
        have hle' : b.toNat + 2 ^ 32 * 0 ≤ x.toNat + 2 ^ 32 * evalLimbs xs := by
          simpa [evalLimbs] using hle
        have hres := sub_borrow_le_tail (sub3Limb x 0 b).1.toNat_lt_size hsub hle'
        simpa using hres
      have ih := ihx [] (sub3Limb x 0 b).2 hstep.2 hle_tail
      have ih' : evalLimbs (subLimbsRaw xs [] (sub3Limb x 0 b).2) +
          (sub3Limb x 0 b).2.toNat = evalLimbs xs := by
        simpa [evalLimbs] using ih
      have hmul : 2 ^ 32 * evalLimbs (subLimbsRaw xs [] (sub3Limb x 0 b).2) +
          2 ^ 32 * (sub3Limb x 0 b).2.toNat = 2 ^ 32 * evalLimbs xs := by
        rw [← Nat.mul_add, ih']
      change (sub3Limb x 0 b).1.toNat + 2 ^ 32 * evalLimbs (subLimbsRaw xs [] (sub3Limb x 0 b).2) + 0 +
          b.toNat = x.toNat + 2 ^ 32 * evalLimbs xs
      omega
    | cons y ys =>
      unfold subLimbsRaw evalLimbs
      have hstep := sub3Limb_correct x y b hb
      dsimp only at hstep ⊢
      have hsub : (sub3Limb x y b).1.toNat + (y.toNat + b.toNat) =
          x.toNat + 2 ^ 32 * (sub3Limb x y b).2.toNat := by omega
      have hle' : (y.toNat + b.toNat) + 2 ^ 32 * evalLimbs ys ≤ x.toNat + 2 ^ 32 * evalLimbs xs := by
        unfold evalLimbs at hle; omega
      have hle_tail := sub_borrow_le_tail (sub3Limb x y b).1.toNat_lt_size hsub hle'
      have ih := ihx ys (sub3Limb x y b).2 hstep.2 (by omega)
      have hmul : 2 ^ 32 * evalLimbs (subLimbsRaw xs ys (sub3Limb x y b).2) +
          2 ^ 32 * evalLimbs ys + 2 ^ 32 * (sub3Limb x y b).2.toNat = 2 ^ 32 * evalLimbs xs := by
        rw [← Nat.mul_add, ← Nat.mul_add, ih]
      omega

/-- **Theorem (`multiLimbNatSub_correct`)**:
    `multiLimbNatSub xs ys` evaluates identically to saturating `evalLimbs xs - evalLimbs ys`
    and produces `WellFormedLimbs`. -/
theorem multiLimbNatSub_correct (xs ys : List UInt32) :
    evalLimbs (multiLimbNatSub xs ys) = evalLimbs xs - evalLimbs ys ∧
    WellFormedLimbs (multiLimbNatSub xs ys) := by
  unfold multiLimbNatSub
  by_cases hble : multiLimbNatBle ys xs
  · simp only [hble, ↓reduceIte]
    have hle : evalLimbs ys ≤ evalLimbs xs := (multiLimbNatBle_correct ys xs).mp hble
    refine ⟨?_, wellFormed_normalize _⟩
    rw [evalLimbs_normalize]
    have hraw := subLimbsRaw_eval xs ys 0 (by decide) (by simpa using hle)
    have h0 : (0 : UInt32).toNat = 0 := rfl
    rw [h0, Nat.add_zero] at hraw
    omega
  · simp only [hble, Bool.false_eq_true, ↓reduceIte]
    have hnle : ¬ evalLimbs ys ≤ evalLimbs xs := fun h =>
      hble ((multiLimbNatBle_correct ys xs).mpr h)
    have hlt : evalLimbs xs < evalLimbs ys := Nat.lt_of_not_le hnle
    refine ⟨?_, rfl⟩
    simp [evalLimbs, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]

private def mulAddU32 (c y carry : UInt32) : UInt32 × UInt32 :=
  let p := mulU32 c y
  let lo := p.1 + carry
  let c1 : UInt32 := if lo < p.1 then 1 else 0
  (lo, p.2 + c1)

private theorem mulAddU32_step_arith {p1 p2 cy c1 lo hi c y : Nat}
    (hc : c < 2 ^ 32) (hy : y < 2 ^ 32) (hcy : cy < 2 ^ 32)
    (_hp1 : p1 < 2 ^ 32) (_hp2 : p2 < 2 ^ 32) (_hlo : lo < 2 ^ 32)
    (_hc1b : c1 ≤ 1)
    (hp : p1 + p2 * 2 ^ 32 = c * y)
    (h1 : c1 * 2 ^ 32 + lo = p1 + cy)
    (hhi : hi = (p2 + c1) % 2 ^ 32) :
    lo + 2 ^ 32 * hi = c * y + cy := by
  have hsum : lo + 2 ^ 32 * (p2 + c1) = c * y + cy := by
    calc lo + 2 ^ 32 * (p2 + c1)
        = (c1 * 2 ^ 32 + lo) + p2 * 2 ^ 32 := by
          rw [Nat.mul_add, Nat.mul_comm (2 ^ 32) p2, Nat.mul_comm (2 ^ 32) c1]; omega
      _ = (p1 + cy) + p2 * 2 ^ 32 := by rw [h1]
      _ = (p1 + p2 * 2 ^ 32) + cy := by omega
      _ = c * y + cy := by rw [hp]
  have hno_ov : p2 + c1 < 2 ^ 32 := by
    by_cases hlt : p2 + c1 < 2 ^ 32
    · exact hlt
    · exfalso
      have hge : 2 ^ 32 ≤ p2 + c1 := Nat.le_of_not_lt hlt
      have hmul : 2 ^ 32 * 2 ^ 32 ≤ 2 ^ 32 * (p2 + c1) := Nat.mul_le_mul_left _ hge
      have h64 : (2 ^ 32 * 2 ^ 32 : Nat) = 2 ^ 64 := by decide
      rw [h64] at hmul
      have hlo_ge : 2 ^ 64 ≤ c * y + cy := by
        rw [← hsum]; exact Nat.le_trans hmul (Nat.le_add_left _ _)
      have hc1' : c ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hc
      have hy1' : y ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hy
      have hcy1' : cy ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hcy
      have hmulmax : c * y ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul hc1' hy1'
      have htot : c * y + cy ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) :=
        Nat.add_le_add hmulmax hcy1'
      have hlt64 : (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) < 2 ^ 64 := by decide
      exact absurd (Nat.le_trans hlo_ge htot) (Nat.not_le_of_gt hlt64)
  rw [hhi, Nat.mod_eq_of_lt hno_ov]
  exact hsum

private theorem mulAddU32_correct (c y carry : UInt32) :
    let r := mulAddU32 c y carry
    r.1.toNat + 2 ^ 32 * r.2.toNat = c.toNat * y.toNat + carry.toNat := by
  unfold mulAddU32
  dsimp only
  have hp : (mulU32 c y).1.toNat + (mulU32 c y).2.toNat * 2 ^ 32 = c.toNat * y.toNat :=
    mulU32_correct c y
  have h1 := (ui32_add_carry_iff_p4 (mulU32 c y).1 carry).2
  have hc1b : (if (mulU32 c y).1 + carry < (mulU32 c y).1 then (1 : UInt32) else 0).toNat ≤ 1 := by
    split <;> decide
  have h1' : (if (mulU32 c y).1 + carry < (mulU32 c y).1 then (1 : UInt32) else 0).toNat * 2 ^ 32 +
      ((mulU32 c y).1 + carry).toNat = (mulU32 c y).1.toNat + carry.toNat := by
    have ht : (if (mulU32 c y).1 + carry < (mulU32 c y).1 then (1 : UInt32) else 0).toNat * 2 ^ 32 =
        if (mulU32 c y).1 + carry < (mulU32 c y).1 then 2 ^ 32 else 0 := by
      split <;> simp
    rw [ht]; exact h1
  have hhi : ((mulU32 c y).2 +
      (if (mulU32 c y).1 + carry < (mulU32 c y).1 then (1 : UInt32) else 0)).toNat =
      ((mulU32 c y).2.toNat +
        (if (mulU32 c y).1 + carry < (mulU32 c y).1 then (1 : UInt32) else 0).toNat) % 2 ^ 32 := by
    rw [UInt32.toNat_add]
  exact mulAddU32_step_arith c.toNat_lt_size y.toNat_lt_size carry.toNat_lt_size
    (mulU32 c y).1.toNat_lt_size (mulU32 c y).2.toNat_lt_size
    ((mulU32 c y).1 + carry).toNat_lt_size hc1b hp h1' hhi

/-- Multiplies a limb list `ys` by a single `UInt32` scalar `c` plus carry-in. -/
def scaleLimbs (c : UInt32) : List UInt32 -> UInt32 -> List UInt32
  | [], carry => if carry == 0 then [] else [carry]
  | y :: ys, carry =>
    let r := mulAddU32 c y carry
    r.1 :: scaleLimbs c ys r.2

private theorem scaleLimbs_eval (c : UInt32) (ys : List UInt32) (carry : UInt32) :
    evalLimbs (scaleLimbs c ys carry) = c.toNat * evalLimbs ys + carry.toNat := by
  induction ys generalizing carry with
  | nil =>
    unfold scaleLimbs evalLimbs
    by_cases hcz : carry == 0
    · simp only [hcz, ↓reduceIte]
      have h0 : carry.toNat = 0 := by rw [beq_iff_eq.mp hcz]; rfl
      rw [h0, Nat.mul_zero, Nat.add_zero]
    · simp only [hcz, Bool.false_eq_true, ↓reduceIte]
      change carry.toNat + 2 ^ 32 * 0 = c.toNat * 0 + carry.toNat
      simp
  | cons y ys ih =>
    unfold scaleLimbs evalLimbs
    have hm := mulAddU32_correct c y carry
    dsimp only at hm ⊢
    rw [ih (mulAddU32 c y carry).2]
    calc (mulAddU32 c y carry).1.toNat + 2 ^ 32 * (c.toNat * evalLimbs ys + (mulAddU32 c y carry).2.toNat)
        = ((mulAddU32 c y carry).1.toNat + 2 ^ 32 * (mulAddU32 c y carry).2.toNat) +
            2 ^ 32 * (c.toNat * evalLimbs ys) := by
          rw [Nat.mul_add]; omega
      _ = (c.toNat * y.toNat + carry.toNat) + 2 ^ 32 * (c.toNat * evalLimbs ys) := by
          rw [hm]
      _ = c.toNat * (y.toNat + 2 ^ 32 * evalLimbs ys) + carry.toNat := by
          rw [Nat.mul_add, Nat.mul_left_comm (2 ^ 32) c.toNat (evalLimbs ys)]; omega

/-- Schoolbook little-endian multi-limb natural number multiplication (raw). -/
def mulLimbsRaw : List UInt32 -> List UInt32 -> List UInt32
  | [], _ => []
  | x :: xs, ys => addLimbsRaw (scaleLimbs x ys 0) (0 :: mulLimbsRaw xs ys) 0

/-- Canonical multi-limb natural number multiplication returning normalized `UInt32` limbs. -/
def multiLimbNatMul (xs ys : List UInt32) : List UInt32 :=
  normalizeLimbs (mulLimbsRaw xs ys)

private theorem evalLimbs_cons (w : UInt32) (ws : List UInt32) :
    evalLimbs (w :: ws) = w.toNat + 2 ^ 32 * evalLimbs ws := rfl

private theorem mulLimbsRaw_eval (xs ys : List UInt32) :
    evalLimbs (mulLimbsRaw xs ys) = evalLimbs xs * evalLimbs ys := by
  induction xs with
  | nil => simp [mulLimbsRaw, evalLimbs]
  | cons x xs ih =>
    unfold mulLimbsRaw
    rw [addLimbsRaw_eval _ _ 0 (by decide)]
    rw [scaleLimbs_eval x ys 0]
    have h0 : (0 : UInt32).toNat = 0 := rfl
    have hev0 : evalLimbs (0 :: mulLimbsRaw xs ys) = 2 ^ 32 * evalLimbs (mulLimbsRaw xs ys) := by
      rw [evalLimbs_cons, h0, Nat.zero_add]
    rw [hev0, ih, h0, Nat.add_zero, Nat.add_zero]
    rw [evalLimbs_cons, Nat.add_mul, Nat.mul_assoc]

/-- **Theorem (`multiLimbNatMul_correct`)**:
    `multiLimbNatMul xs ys` evaluates identically to `evalLimbs xs * evalLimbs ys` and
    produces `WellFormedLimbs`. -/
theorem multiLimbNatMul_correct (xs ys : List UInt32) :
    evalLimbs (multiLimbNatMul xs ys) = evalLimbs xs * evalLimbs ys ∧
    WellFormedLimbs (multiLimbNatMul xs ys) := by
  unfold multiLimbNatMul
  refine ⟨?_, wellFormed_normalize _⟩
  rw [evalLimbs_normalize, mulLimbsRaw_eval]

/-- Decodes a single little-endian `UInt32` into its 4 bytes (`UInt8`). -/
def decodeWord4 (w : UInt32) : List UInt8 :=
  [ UInt8.ofNat (w.toNat % 2 ^ 8),
    UInt8.ofNat ((w.toNat / 2 ^ 8) % 2 ^ 8),
    UInt8.ofNat ((w.toNat / 2 ^ 16) % 2 ^ 8),
    UInt8.ofNat ((w.toNat / 2 ^ 24) % 2 ^ 8) ]

/-- Encodes 4 bytes into a little-endian `UInt32`. -/
def encodeWord4 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24)

/-- Decodes a little-endian `UInt32` word slice truncated to `byteLen` UTF-8 bytes. -/
def decodeStringWords (byteLen : Nat) (words : List UInt32) : List UInt8 :=
  (words.flatMap decodeWord4).take byteLen

/-- Checks byte-length and little-endian word-array equality for packed GPU `String` literals. -/
def stringLitWordsEq (len1 : Nat) (w1 : List UInt32) (len2 : Nat) (w2 : List UInt32) : Bool :=
  (len1 == len2) && (w1 == w2)

/-- Zero-padding and exact-word-count invariant for GPU `String` literals:
    - every non-trivial word sequence has length `(byteLen + 3) / 4`;
    - padding bytes at indices `>= byteLen` inside `words.flatMap decodeWord4` are `0`. -/
def ZeroPaddedStringWords (byteLen : Nat) (words : List UInt32) : Prop :=
  words.length = (byteLen + 3) / 4 ∧
  ∀ i, byteLen ≤ i -> (words.flatMap decodeWord4)[i]? = none ∨
    (words.flatMap decodeWord4)[i]? = some 0

private theorem decodeWord4_injective {u v : UInt32} (h : decodeWord4 u = decodeWord4 v) :
    u = v := by
  unfold decodeWord4 at h
  simp only [List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have hn0 : u.toNat % 2 ^ 8 = v.toNat % 2 ^ 8 := by
    have := congrArg UInt8.toNat h0
    simpa [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2 ^ 8))] using this
  have hn1 : (u.toNat / 2 ^ 8) % 2 ^ 8 = (v.toNat / 2 ^ 8) % 2 ^ 8 := by
    have := congrArg UInt8.toNat h1
    simpa [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2 ^ 8))] using this
  have hn2 : (u.toNat / 2 ^ 16) % 2 ^ 8 = (v.toNat / 2 ^ 16) % 2 ^ 8 := by
    have := congrArg UInt8.toNat h2
    simpa [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2 ^ 8))] using this
  have hn3 : (u.toNat / 2 ^ 24) % 2 ^ 8 = (v.toNat / 2 ^ 24) % 2 ^ 8 := by
    have := congrArg UInt8.toNat h3
    simpa [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2 ^ 8))] using this
  have hreconstruct (x : UInt32) :
      x.toNat = x.toNat % 2 ^ 8 +
        ((x.toNat / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 +
        ((x.toNat / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
        ((x.toNat / 2 ^ 24) % 2 ^ 8) * 2 ^ 24 := by
    have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
    have hq3 : x.toNat / 2 ^ 24 < 2 ^ 8 := by
      have hp : 2 ^ 8 * 2 ^ 24 = 2 ^ 32 := by decide
      rw [← hp] at hx
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hx
    have hm3 : (x.toNat / 2 ^ 24) % 2 ^ 8 = x.toNat / 2 ^ 24 := Nat.mod_eq_of_lt hq3
    rw [hm3]
    have hstep0 : x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8) * 2 ^ 8 = x.toNat := by
      rw [Nat.mul_comm]; exact Nat.mod_add_div x.toNat (2 ^ 8)
    have hstep1 : (x.toNat / 2 ^ 8) % 2 ^ 8 + ((x.toNat / 2 ^ 8) / 2 ^ 8) * 2 ^ 8 =
        x.toNat / 2 ^ 8 := by
      rw [Nat.mul_comm]; exact Nat.mod_add_div _ (2 ^ 8)
    have hstep2 : (x.toNat / 2 ^ 16) % 2 ^ 8 + ((x.toNat / 2 ^ 16) / 2 ^ 8) * 2 ^ 8 =
        x.toNat / 2 ^ 16 := by
      rw [Nat.mul_comm]; exact Nat.mod_add_div _ (2 ^ 8)
    have hd16 : (x.toNat / 2 ^ 8) / 2 ^ 8 = x.toNat / 2 ^ 16 := by
      rw [Nat.div_div_eq_div_mul]
    have hd24 : (x.toNat / 2 ^ 16) / 2 ^ 8 = x.toNat / 2 ^ 24 := by
      rw [Nat.div_div_eq_div_mul]
    rw [hd16] at hstep1
    rw [hd24] at hstep2
    have hmul1 : (((x.toNat / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 +
        ((x.toNat / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
        (x.toNat / 2 ^ 24) * 2 ^ 24) = (x.toNat / 2 ^ 8) * 2 ^ 8 := by
      have p1 : (2 ^ 8 * 2 ^ 8 : Nat) = 2 ^ 16 := by decide
      have p2 : (2 ^ 8 * 2 ^ 16 : Nat) = 2 ^ 24 := by decide
      calc ((x.toNat / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 +
            ((x.toNat / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
            (x.toNat / 2 ^ 24) * 2 ^ 24
          = ((x.toNat / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 +
            (((x.toNat / 2 ^ 16) % 2 ^ 8) + (x.toNat / 2 ^ 24) * 2 ^ 8) * 2 ^ 16 := by
              rw [Nat.add_mul, Nat.mul_assoc, p2, Nat.add_assoc]
        _ = ((x.toNat / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 + (x.toNat / 2 ^ 16) * 2 ^ 16 := by
              rw [hstep2]
        _ = ((x.toNat / 2 ^ 8) % 2 ^ 8 + (x.toNat / 2 ^ 16) * 2 ^ 8) * 2 ^ 8 := by
              rw [Nat.add_mul, Nat.mul_assoc, p1]
        _ = (x.toNat / 2 ^ 8) * 2 ^ 8 := by rw [hstep1]
    omega
  exact ui32_eq_of_toNat (by rw [hreconstruct u, hreconstruct v, hn0, hn1, hn2, hn3])

private theorem flatMap_decodeWord4_injective :
    ∀ w1 w2 : List UInt32,
      w1.flatMap decodeWord4 = w2.flatMap decodeWord4 -> w1 = w2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [decodeWord4] at h
  | _ :: _, [], h => by simp [decodeWord4] at h
  | u :: us, v :: vs, h => by
    simp only [List.flatMap_cons] at h
    have hlen : (decodeWord4 u).length = (decodeWord4 v).length := by simp [decodeWord4]
    have hsplit := List.append_inj h hlen
    rw [decodeWord4_injective hsplit.1, flatMap_decodeWord4_injective us vs hsplit.2]

private theorem flatMap_decodeWord4_length (ws : List UInt32) :
    (ws.flatMap decodeWord4).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ih]
    have hl : (decodeWord4 w).length = 4 := by rfl
    omega

private theorem list_eq_of_getElem?_eq {α : Type} :
    ∀ l1 l2 : List α, (∀ i : Nat, l1[i]? = l2[i]?) -> l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by have h0 := h 0; simp at h0
  | _ :: _, [], h => by have h0 := h 0; simp at h0
  | _ :: xs, _ :: ys, h => by
    have h0 := h 0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    rw [h0, list_eq_of_getElem?_eq xs ys (fun i => by simpa using h (i + 1))]

/-- **Theorem (`stringLitWordsEq_sound`)**:
    Under the `ZeroPaddedStringWords` invariant, comparing `(len, words)` via
    `stringLitWordsEq` holds iff the decoded UTF-8 byte lists are identical. -/
theorem stringLitWordsEq_sound
    {len1 len2 : Nat} {w1 w2 : List UInt32}
    (hp1 : ZeroPaddedStringWords len1 w1)
    (hp2 : ZeroPaddedStringWords len2 w2) :
    stringLitWordsEq len1 w1 len2 w2 = true ↔
      decodeStringWords len1 w1 = decodeStringWords len2 w2 := by
  unfold stringLitWordsEq
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hlen, hw⟩
    rw [hlen, hw]
  · intro hdec
    unfold decodeStringWords at hdec
    have hlen1 : len1 ≤ (w1.flatMap decodeWord4).length := by
      rw [flatMap_decodeWord4_length, hp1.1]; omega
    have hlen2 : len2 ≤ (w2.flatMap decodeWord4).length := by
      rw [flatMap_decodeWord4_length, hp2.1]; omega
    have hlenEq : len1 = len2 := by
      have hL := congrArg List.length hdec
      rw [List.length_take_of_le hlen1, List.length_take_of_le hlen2] at hL
      exact hL
    refine ⟨hlenEq, flatMap_decodeWord4_injective w1 w2 ?_⟩
    apply list_eq_of_getElem?_eq
    intro i
    by_cases hi : i < len1
    · have h1 := List.getElem?_take (l := w1.flatMap decodeWord4) (i := len1) (j := i)
      have h2 := List.getElem?_take (l := w2.flatMap decodeWord4) (i := len2) (j := i)
      have hi2 : i < len2 := by rw [← hlenEq]; exact hi
      simp only [hi, hi2, ↓reduceIte] at h1 h2
      rw [← h1, ← h2, hdec]
    · have hge1 : len1 ≤ i := Nat.le_of_not_lt hi
      have hge2 : len2 ≤ i := by rw [← hlenEq]; exact hge1
      have hwlen : w1.length = w2.length := by rw [hp1.1, hp2.1, hlenEq]
      have hfl : (w1.flatMap decodeWord4).length = (w2.flatMap decodeWord4).length := by
        rw [flatMap_decodeWord4_length, flatMap_decodeWord4_length, hwlen]
      by_cases hlt : i < (w1.flatMap decodeWord4).length
      · have hlt2 : i < (w2.flatMap decodeWord4).length := by rw [← hfl]; exact hlt
        rcases hp1.2 i hge1 with hnone | hs1
        · exact absurd hlt (Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp hnone))
        · rcases hp2.2 i hge2 with hnone | hs2
          · exact absurd hlt2 (Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp hnone))
          · rw [hs1, hs2]
      · have hge_len1 : (w1.flatMap decodeWord4).length ≤ i := Nat.le_of_not_lt hlt
        have hge_len2 : (w2.flatMap decodeWord4).length ≤ i := by rw [← hfl]; exact hge_len1
        rw [List.getElem?_eq_none hge_len1, List.getElem?_eq_none hge_len2]

/-- Extended kernel expression language supporting structure field projections `.proj`. -/
inductive P4Expr where
  | bvar (idx : Nat)
  | fvar (id : Nat)
  | sort (lvl : Nat)
  | const (cid : Nat) (us : List Nat)
  | app (fn arg : P4Expr)
  | lam (dom body : P4Expr)
  | forallE (dom cod : P4Expr)
  | proj (structCid fieldIdx : Nat) (s : P4Expr)
  deriving DecidableEq, Repr, Inhabited

/-- Multi-argument spine builder for `P4Expr`. -/
def p4MkAppN (fn : P4Expr) (args : List P4Expr) : P4Expr :=
  args.foldl P4Expr.app fn

/-- Generalized single-constructor structure descriptor supporting `k` fields (`numFields`). -/
structure MultiFieldStructSpec where
  structCid : Nat
  ctorCid : Nat
  numParams : Nat
  numFields : Nat
  allowsEta : Bool
  isProp : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Eligibility predicate for `k`-field non-`Prop` single-constructor structure eta. -/
def MultiFieldEtaEligible (sd : MultiFieldStructSpec) : Prop :=
  sd.allowsEta = true ∧ sd.isProp = false

/-- Builds the canonical `k`-field projection list `[.proj structCid 0 s, ..., .proj structCid (k-1) s]`. -/
def mkStructProjFields (structCid : Nat) (s : P4Expr) (k : Nat) : List P4Expr :=
  (List.range k).map (fun i => P4Expr.proj structCid i s)

/-- Environment for `k`-field structure eta soundness. -/
structure P4Env where
  decls : Array SDecl
  structs : List MultiFieldStructSpec
  deriving Repr, Inhabited

mutual
  /-- Declarative kernel definitional equality with `k`-field non-`Prop` structure eta. -/
  inductive P4DefEq (env : P4Env) : P4Expr -> P4Expr -> Prop
    | refl (a : P4Expr) : P4DefEq env a a
    | symm {a b : P4Expr} : P4DefEq env a b -> P4DefEq env b a
    | trans {a b c : P4Expr} : P4DefEq env a b -> P4DefEq env b c -> P4DefEq env a c
    | app {f₁ f₂ a₁ a₂ : P4Expr} :
        P4DefEq env f₁ f₂ -> P4DefEq env a₁ a₂ -> P4DefEq env (.app f₁ a₁) (.app f₂ a₂)
    | lam {d₁ d₂ b₁ b₂ : P4Expr} :
        P4DefEq env d₁ d₂ -> P4DefEq env b₁ b₂ -> P4DefEq env (.lam d₁ b₁) (.lam d₂ b₂)
    | forallE {d₁ d₂ c₁ c₂ : P4Expr} :
        P4DefEq env d₁ d₂ -> P4DefEq env c₁ c₂ -> P4DefEq env (.forallE d₁ c₁) (.forallE d₂ c₂)
    | proj {scid fidx : Nat} {s₁ s₂ : P4Expr} :
        P4DefEq env s₁ s₂ -> P4DefEq env (.proj scid fidx s₁) (.proj scid fidx s₂)
    | structEtaK {ctx : List P4Expr} {sd : MultiFieldStructSpec}
        {t : P4Expr} {us : List Nat} {params : List P4Expr} :
        sd ∈ env.structs ->
        MultiFieldEtaEligible sd ->
        params.length = sd.numParams ->
        P4HasType env ctx t (p4MkAppN (.const sd.structCid us) params) ->
        P4DefEq env t (p4MkAppN (.const sd.ctorCid us)
          (params ++ mkStructProjFields sd.structCid t sd.numFields))

  /-- Declarative kernel typing judgment for `P4Expr` (`structEtaK` premise). -/
  inductive P4HasType (env : P4Env) : List P4Expr -> P4Expr -> P4Expr -> Prop
    | sort (ctx : List P4Expr) (u : Nat) :
        P4HasType env ctx (.sort u) (.sort (u + 1))
    | fvar {ctx : List P4Expr} {id : Nat} {ty : P4Expr} :
        P4HasType env ctx (.fvar id) ty
    | const {ctx : List P4Expr} {cid : Nat} {us : List Nat} {ty : P4Expr} :
        P4HasType env ctx (.const cid us) ty
    | app {ctx : List P4Expr} {f a A B : P4Expr} :
        P4HasType env ctx f (.forallE A B) ->
        P4HasType env ctx a A ->
        P4HasType env ctx (.app f a) B
    | proj {ctx : List P4Expr} {scid fidx : Nat} {s ty : P4Expr} :
        P4HasType env ctx (.proj scid fidx s) ty
    | conv {ctx : List P4Expr} {e A B : P4Expr} :
        P4HasType env ctx e A ->
        P4DefEq env A B ->
        P4HasType env ctx e B
end

private theorem p4MkAppN_app_congr {env : P4Env} {f1 f2 : P4Expr}
    (hf : P4DefEq env f1 f2) :
    ∀ a1 a2 : List P4Expr, a1.length = a2.length ->
      (∀ i, i < a1.length -> ∀ x y, a1[i]? = some x -> a2[i]? = some y -> P4DefEq env x y) ->
      P4DefEq env (p4MkAppN f1 a1) (p4MkAppN f2 a2)
  | [], [], _, _ => hf
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hargs => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hxy : P4DefEq env x y := hargs 0 (Nat.zero_lt_succ _) x y rfl rfl
    have hfn : P4DefEq env (.app f1 x) (.app f2 y) := .app hf hxy
    exact p4MkAppN_app_congr hfn xs ys hlen (fun i hi u v hu hv =>
      hargs (i + 1) (Nat.succ_lt_succ hi) u v hu hv)

/-- Executable WGSL-side `k`-field structure eta check matching a constructor spine
    `ctor us (params ++ fields)` against `t`, where every field `i < k` satisfies `fields[i] ≈ proj_i(t)`. -/
def multiFieldStructEtaOk (sd : MultiFieldStructSpec) (_us : List Nat)
    (params fields : List P4Expr) (t : P4Expr) (fieldEq : P4Expr -> P4Expr -> Bool) : Bool :=
  sd.allowsEta && !sd.isProp &&
  (params.length == sd.numParams) &&
  (fields.length == sd.numFields) &&
  ((List.range sd.numFields).all fun i =>
    match fields[i]? with
    | some fi => fieldEq fi (.proj sd.structCid i t)
    | none => false)

/-- **Theorem (`multiFieldStructEta_sound`)**:
    When `multiFieldStructEtaOk` succeeds for a registered non-`Prop` single-constructor
    `k`-field structure `sd` (`t` typed at `sd.structCid`) and `fieldEq` is sound for `P4DefEq`,
    both `t ≈ ctor(params ++ fields)` and `ctor(params ++ fields) ≈ t` hold in `P4DefEq`. -/
theorem multiFieldStructEta_sound
    {env : P4Env} {ctx : List P4Expr} {sd : MultiFieldStructSpec}
    {t : P4Expr} {us : List Nat} {params fields : List P4Expr}
    {fieldEq : P4Expr -> P4Expr -> Bool}
    (hmem : sd ∈ env.structs)
    (ht : P4HasType env ctx t (p4MkAppN (.const sd.structCid us) params))
    (hfeq : ∀ a b, fieldEq a b = true -> P4DefEq env a b)
    (hok : multiFieldStructEtaOk sd us params fields t fieldEq = true) :
    P4DefEq env t (p4MkAppN (.const sd.ctorCid us) (params ++ fields)) ∧
    P4DefEq env (p4MkAppN (.const sd.ctorCid us) (params ++ fields)) t := by
  unfold multiFieldStructEtaOk at hok
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true] at hok
  rcases hok with ⟨⟨⟨⟨ha, hnp⟩, hplen⟩, hflen⟩, hfields⟩
  have helig : MultiFieldEtaEligible sd := ⟨ha, hnp⟩
  have heta : P4DefEq env t
      (p4MkAppN (.const sd.ctorCid us) (params ++ mkStructProjFields sd.structCid t sd.numFields)) :=
    .structEtaK hmem helig hplen ht
  have hcanon_len : (mkStructProjFields sd.structCid t sd.numFields).length = sd.numFields := by
    simp [mkStructProjFields]
  have hcomb_len :
      (params ++ mkStructProjFields sd.structCid t sd.numFields).length = (params ++ fields).length := by
    simp [hcanon_len, hflen]
  have hcongr : P4DefEq env
      (p4MkAppN (.const sd.ctorCid us) (params ++ mkStructProjFields sd.structCid t sd.numFields))
      (p4MkAppN (.const sd.ctorCid us) (params ++ fields)) := by
    refine p4MkAppN_app_congr (.refl _) _ _ hcomb_len ?_
    intro i hi x y hx hy
    by_cases hp : i < params.length
    · rw [List.getElem?_append_left hp] at hx hy
      rw [hx] at hy
      injection hy with hxy
      rw [hxy]
      exact .refl y
    · have hge : params.length ≤ i := Nat.le_of_not_lt hp
      rw [List.getElem?_append_right hge] at hx hy
      let j := i - params.length
      have hj : j < sd.numFields := by
        simp only [List.length_append, hcanon_len] at hi
        dsimp [j]; omega
      have hxr : (mkStructProjFields sd.structCid t sd.numFields)[j]? =
          some (.proj sd.structCid j t) := by
        simp [mkStructProjFields, hj]
      rw [hxr] at hx
      injection hx with hxe
      have hfi := hfields j (List.mem_range.mpr hj)
      change (match fields[j]? with
        | some fi => fieldEq fi (.proj sd.structCid j t)
        | none => false) = true at hfi
      have hy' : fields[j]? = some y := hy
      rw [hy'] at hfi
      rw [← hxe]
      exact .symm (hfeq y (.proj sd.structCid j t) hfi)
  have hres : P4DefEq env t (p4MkAppN (.const sd.ctorCid us) (params ++ fields)) :=
    .trans heta hcongr
  exact ⟨hres, .symm hres⟩


/-! ### 4. `CGSNAP03` Stat Manifest & Split GPU-First Load -/

/-- Manifest record stored in `CGSNAP03` for each `.olean` file in the closure. -/
structure StatManifestEntry where
  pathId : Nat
  sizeBytes : Nat
  mtimeSec : Nat
  mtimeNsec : Nat
  contentDigest : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Live filesystem metadata & content for a `.olean` file. -/
structure LiveOleanFile where
  pathId : Nat
  sizeBytes : Nat
  mtimeSec : Nat
  mtimeNsec : Nat
  bytes : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Fast stat check comparing path, byte size, and nanosecond mtime against the manifest. -/
def statMatchesEntry (e : StatManifestEntry) (f : LiveOleanFile) : Bool :=
  (e.pathId == f.pathId) && (e.sizeBytes == f.sizeBytes) &&
    (e.mtimeSec == f.mtimeSec) && (e.mtimeNsec == f.mtimeNsec)

/-- Checks whether every manifest entry matches its corresponding live file stat. -/
def statManifestFastOk : List StatManifestEntry -> List LiveOleanFile -> Bool
  | [], [] => true
  | e :: es, f :: fs => statMatchesEntry e f && statManifestFastOk es fs
  | _, _ => false

/-- Verified resolution: fast-path hits when stat-manifest matches; otherwise full content rehash
    (`hashFn f.bytes == e.contentDigest`). -/
def resolveStatManifest (hashFn : List UInt8 -> Nat)
    (manifest : List StatManifestEntry) (live : List LiveOleanFile) : Bool :=
  if statManifestFastOk manifest live then true
  else
    manifest.length == live.length &&
      (List.zip manifest live).all (fun p => hashFn p.2.bytes == p.1.contentDigest)

/-- Filesystem stat-cache assumption: matching `(pathId, sizeBytes, mtimeSec, mtimeNsec)` implies
    matching `hashFn f.bytes = e.contentDigest` (whereas any mismatch triggers content rehash). -/
def StatCacheConsistent (hashFn : List UInt8 -> Nat)
    (manifest : List StatManifestEntry) (live : List LiveOleanFile) : Prop :=
  ∀ e f, (e, f) ∈ List.zip manifest live ->
    statMatchesEntry e f = true -> hashFn f.bytes = e.contentDigest

/-- **Theorem (`cgsnap03StatManifest_sound`)**:
    Whenever `resolveStatManifest hashFn manifest live = true` under `StatCacheConsistent`:
    1. Every entry `i` matches its `contentDigest` via `hashFn f.bytes = e.contentDigest`
       (either via verified stat fast-path or via fallback full content rehash).
    2. On any path/size/mtime mismatch (`statManifestFastOk = false`), the fast path is skipped and
       acceptance requires exact `hashFn f.bytes = e.contentDigest` across all files. -/
theorem cgsnap03StatManifest_sound
    (hashFn : List UInt8 -> Nat)
    (manifest : List StatManifestEntry) (live : List LiveOleanFile)
    (hstat : StatCacheConsistent hashFn manifest live) :
    (statManifestFastOk manifest live = true ->
      manifest.length = live.length ∧
      ∀ e f, (e, f) ∈ List.zip manifest live -> hashFn f.bytes = e.contentDigest) ∧
    (statManifestFastOk manifest live = false ->
      (resolveStatManifest hashFn manifest live = true ↔
        manifest.length = live.length ∧
        ∀ e f, (e, f) ∈ List.zip manifest live -> hashFn f.bytes = e.contentDigest)) ∧
    (resolveStatManifest hashFn manifest live = true ->
      manifest.length = live.length ∧
      ∀ e f, (e, f) ∈ List.zip manifest live -> hashFn f.bytes = e.contentDigest) := by
  have hfast : statManifestFastOk manifest live = true ->
      manifest.length = live.length ∧
      ∀ e f, (e, f) ∈ List.zip manifest live -> hashFn f.bytes = e.contentDigest := by
    intro hok
    induction manifest generalizing live with
    | nil =>
      cases live with
      | nil => exact ⟨rfl, fun _ _ hm => by simp at hm⟩
      | cons _ _ => simp [statManifestFastOk] at hok
    | cons e es ih =>
      cases live with
      | nil => simp [statManifestFastOk] at hok
      | cons f fs =>
        unfold statManifestFastOk at hok
        simp only [Bool.and_eq_true] at hok
        have hstat_tail : StatCacheConsistent hashFn es fs := fun e' f' hm hst =>
          hstat e' f' (by simp [hm]) hst
        obtain ⟨hlen, hmem⟩ := ih fs hstat_tail hok.2
        refine ⟨by simp [hlen], fun e' f' hm => ?_⟩
        simp only [List.zip_cons_cons, List.mem_cons] at hm
        rcases hm with hpair | htail
        · have he : e' = e := congrArg Prod.fst hpair
          have hf : f' = f := congrArg Prod.snd hpair
          subst he; subst hf
          exact hstat e' f' (by simp) hok.1
        · exact hmem e' f' htail
  have hslow : statManifestFastOk manifest live = false ->
      (resolveStatManifest hashFn manifest live = true ↔
        manifest.length = live.length ∧
        ∀ e f, (e, f) ∈ List.zip manifest live -> hashFn f.bytes = e.contentDigest) := by
    intro hf
    unfold resolveStatManifest
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    constructor
    · rintro ⟨hlen, hall⟩
      refine ⟨hlen, fun e f hm => ?_⟩
      exact hall (e, f) hm
    · rintro ⟨hlen, hall⟩
      refine ⟨hlen, fun p hm => ?_⟩
      exact hall p.1 p.2 hm
  refine ⟨hfast, hslow, ?_⟩
  intro hres
  cases hf : statManifestFastOk manifest live
  · exact (hslow hf).mp hres
  · exact hfast hf

/-- `CGSNAP03` magic header identifier (`0x43475333`). -/
def cgsnap03Magic : Nat := 0x43475333

/-- GPU-first half of a split `CGSNAP03` snapshot packet (`Arena` + GPU `ConstDecl`s + digests). -/
structure GpuFirstPacketV3 where
  magic : Nat
  version : Nat
  pers : SoATier
  gpuDecls : Array GpuConstDecl
  totalDecls : Nat
  closureHash : Nat
  statDigest : Nat
  deriving Repr, Inhabited

/-- Host half of a split `CGSNAP03` snapshot loaded for delegated fallback checking. -/
structure HostEnvSnapshotV3 where
  magic : Nat
  version : Nat
  env : KEnv
  hostClosureHash : Nat
  deriving Repr, Inhabited

/-- Closure-hash and stat-digest binding invariant for split `CGSNAP03` restoration. -/
def DualSnapshotBindingV3 (canonPers : SoATier) (canonEnv : KEnv)
    (packet : GpuFirstPacketV3) (host : HostEnvSnapshotV3)
    (expectedHash expectedStatDigest : Nat) : Prop :=
  (packet.magic = cgsnap03Magic -> packet.version = 3 ->
    packet.closureHash = expectedHash -> packet.statDigest = expectedStatDigest ->
    packet.pers = canonPers ∧
    packet.totalDecls = canonEnv.size ∧
    packet.gpuDecls.size = canonEnv.size ∧
    EnvSound packet.pers packet.gpuDecls canonEnv) ∧
  (host.magic = cgsnap03Magic -> host.version = 3 ->
    host.hostClosureHash = expectedHash -> host.env = canonEnv)

/-- Outcome of split GPU-first `CGSNAP03` restoration and verification. -/
structure SplitLoadOutcome where
  gpuStageLoaded : Bool
  hostStageLoaded : Bool
  accepted : Bool
  deriving DecidableEq, Repr, Inhabited

private def checkJobsFrom (pred : Nat -> Bool) : Nat -> Bool
  | 0 => true
  | k + 1 => pred k && checkJobsFrom pred k

private theorem checkJobsFrom_iff (pred : Nat -> Bool) (n : Nat) :
    checkJobsFrom pred n = true ↔ ∀ i, i < n -> pred i = true := by
  induction n with
  | zero => simp [checkJobsFrom]
  | succ k ih =>
    unfold checkJobsFrom
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hk, hrest⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hrest i hlt
      · exact hk
    · intro hall
      exact ⟨hall k (Nat.lt_succ_self k), fun i hi => hall i (Nat.lt_succ_of_lt hi)⟩

/-- Executes `CGSNAP03` split GPU-first verification:
    Stage 1 validates the GPU packet and dispatches GPU verification first (`gpuPass`);
    Stage 2 loads `HostEnvSnapshotV3` for any jobs not conclusively handled by GPU, verifying
    each delegated job against the exact host environment. -/
def verifyCgsnap03Split (packet : GpuFirstPacketV3) (host : HostEnvSnapshotV3)
    (expectedHash expectedStatDigest : Nat)
    (gpuPass hostCheck : Nat -> Bool) : SplitLoadOutcome :=
  let gpuHeaderOk :=
    (packet.magic == cgsnap03Magic) && (packet.version == 3) &&
    (packet.closureHash == expectedHash) && (packet.statDigest == expectedStatDigest) &&
    (packet.gpuDecls.size == packet.totalDecls)
  if !gpuHeaderOk then
    { gpuStageLoaded := false, hostStageLoaded := false, accepted := false }
  else
    let hostHeaderOk :=
      (host.magic == cgsnap03Magic) && (host.version == 3) &&
      (host.hostClosureHash == expectedHash) && (host.env.size == packet.totalDecls)
    if !hostHeaderOk then
      { gpuStageLoaded := true, hostStageLoaded := false, accepted := false }
    else
      let ok := checkJobsFrom (fun i => gpuPass i || hostCheck i) packet.totalDecls
      { gpuStageLoaded := true, hostStageLoaded := true, accepted := ok }

/-- **Theorem (`cgsnap03SplitLoad_sound`)**:
    Under `DualSnapshotBindingV3`:
    1. Any GPU or host header/version/closure-hash/stat-digest/size mismatch rejects
       (`accepted = false`, with `hostStageLoaded = false` / `gpuStageLoaded = false`).
    2. When both split stages load cleanly (`gpuStageLoaded = true ∧ hostStageLoaded = true`),
       `packet.pers = canonPers`, `host.env = canonEnv`, `EnvSound packet.pers packet.gpuDecls canonEnv`,
       and `accepted = true ↔ ∀ i d, canonEnv[i]? = some d -> DeclVerified canonEnv d ∧ ∃ u, HasType canonEnv [] d.ty (.sort u)`
       (with `gpuPass` alone implying `DeclVerified` on GPU-accepted jobs, and host fallback covering
       all remaining jobs). -/
theorem cgsnap03SplitLoad_sound
    {canonPers : SoATier} {canonEnv : KEnv}
    {packet : GpuFirstPacketV3} {host : HostEnvSnapshotV3}
    {expectedHash expectedStatDigest : Nat}
    {gpuPass hostCheck : Nat -> Bool}
    (hbind : DualSnapshotBindingV3 canonPers canonEnv packet host expectedHash expectedStatDigest)
    (hgpuSound : ∀ i d, canonEnv[i]? = some d -> gpuPass i = true -> DeclVerified canonEnv d)
    (hhostSound : ∀ i d, canonEnv[i]? = some d -> hostCheck i = true -> DeclVerified canonEnv d)
    (hhostComplete : ∀ i d, canonEnv[i]? = some d -> DeclVerified canonEnv d -> hostCheck i = true) :
    let out := verifyCgsnap03Split packet host expectedHash expectedStatDigest gpuPass hostCheck
    (out.accepted = true -> out.gpuStageLoaded = true ∧ out.hostStageLoaded = true) ∧
    (out.gpuStageLoaded = true ->
      packet.pers = canonPers ∧
      packet.totalDecls = canonEnv.size ∧
      EnvSound packet.pers packet.gpuDecls canonEnv) ∧
    (out.gpuStageLoaded = true -> out.hostStageLoaded = true ->
      host.env = canonEnv ∧
      (out.accepted = true ↔
        ∀ (i : Nat) (d : ConstDecl), canonEnv[i]? = some d ->
          DeclVerified canonEnv d ∧ (∃ u, HasType canonEnv [] d.ty (.sort u)))) := by
  unfold verifyCgsnap03Split
  dsimp only
  cases hgpuH :
      ((packet.magic == cgsnap03Magic) && (packet.version == 3) &&
       (packet.closureHash == expectedHash) && (packet.statDigest == expectedStatDigest) &&
       (packet.gpuDecls.size == packet.totalDecls))
  · simp only [Bool.not_false, ↓reduceIte]
    exact ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hgpuH' := hgpuH
    simp only [Bool.and_eq_true, beq_iff_eq] at hgpuH'
    rcases hgpuH' with ⟨⟨⟨⟨hpm, hpv⟩, hph⟩, hps⟩, _⟩
    obtain ⟨hpers, hlen, _, henv⟩ := hbind.1 hpm hpv hph hps
    cases hhostH :
        ((host.magic == cgsnap03Magic) && (host.version == 3) &&
         (host.hostClosureHash == expectedHash) && (host.env.size == packet.totalDecls))
    · simp only [Bool.not_false, ↓reduceIte]
      exact ⟨(fun h => by cases h), (fun _ => ⟨hpers, hlen, henv⟩), (fun _ h => by cases h)⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hhostH' := hhostH
      simp only [Bool.and_eq_true, beq_iff_eq] at hhostH'
      rcases hhostH' with ⟨⟨⟨hhm, hhv⟩, hhh⟩, _⟩
      have henvEq := hbind.2 hhm hhv hhh
      refine ⟨(fun _ => ⟨trivial, trivial⟩), (fun _ => ⟨hpers, hlen, henv⟩), (fun _ _ => ⟨henvEq, ?_⟩)⟩
      rw [checkJobsFrom_iff, hlen]
      constructor
      · intro hall i d hlu
        have hi : i < canonEnv.size := by
          by_cases hlt : i < canonEnv.size
          · exact hlt
          · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hlu; cases hlu
        have hdisj := hall i hi
        rw [Bool.or_eq_true] at hdisj
        have hdv : DeclVerified canonEnv d := by
          rcases hdisj with hg | hh
          · exact hgpuSound i d hlu hg
          · exact hhostSound i d hlu hh
        obtain ⟨f1, u, hty⟩ := hdv.1
        exact ⟨hdv, ⟨u, inferSpec_hasType canonEnv f1 [] d.ty (.sort u) hty⟩⟩
      · intro hall i hi
        have hget : i < canonEnv.size := hi
        let d := canonEnv[i]
        have hlu : canonEnv[i]? = some d := Array.getElem?_eq_getElem hget
        have hh := hhostComplete i d hlu (hall i d hlu).1
        simp [hh]

end ConGpuProof
