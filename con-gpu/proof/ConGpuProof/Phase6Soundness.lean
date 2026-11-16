/-
ConGpuProof.Phase6Soundness
===========================
Formal Lean 4 verification for `con-gpu` Phase 6 optimizations:
  1. Selective Tier-2 Promotion & Direct Step-Cutoff Delegation:
     `selectiveTier2Promotion_sound`,
     `tier1StepCutoffDirectDelegate_sound`,
     `hybridPartitionConservation`.
  2. Vulkan Storage Binding & Occupancy Arithmetic:
     `tier2Wgs124FitsVulkan`,
     `tier1BindingClamp_sound`,
     `adaptiveScratchClamping_sound`.
  3. Parallel Columnar `HostSection` Decode & Frozen `ConsMap` Determinism:
     `parallelColDecode_exact`,
     `uniqueRowConsInsert_exact`.
-/

import ConGpuProof.Phase4Soundness

namespace ConGpuProof

/-! ### 1. Selective Tier-2 Promotion & Direct Step-Cutoff Delegation -/

/-- Phase 6 selective Tier-2 promotion guard (`typecheck.rs`):
    promotes ONLY `STATUS_DELEGATE` (`3`) jobs whose reason is `REASON_STACK_BUDGET` (`4`)
    or `REASON_SCRATCH_BUDGET` (`5`), never `status = 0` cutoffs or `REASON_STEP_BUDGET` (`3`). -/
def isSelectiveTier2Promotable (t1s t1r : Nat) : Bool :=
  (t1s == 3) && (t1r == reasonStackBudget || t1r == reasonScratchBudget)

/-- Normalizes Tier-1 cutoff (`status = 0`) to `(STATUS_DELEGATE = 3, REASON_STEP_BUDGET = 3)`
    when delegating directly to the host verifier so `delegate_reasons[3]` accounts cleanly. -/
def normalizeDirectDelegateStatusReason (t1s t1r : Nat) : Nat × Nat :=
  if t1s == 0 then (3, reasonStepBudget) else (t1s, t1r)

/-- Evaluates one job under Phase 6 selective Tier-2 scheduling:
    - `t1s = 1`: accepted by Tier-1 GPU.
    - `t1s = 2`: rejected by Tier-1 GPU.
    - `isSelectiveTier2Promotable t1s t1r`: promoted to Tier-2 (`124` WGs), then host on non-1/2.
    - otherwise (including `t1s = 0` cutoff and `REASON_STEP_BUDGET = 3`): delegated directly
      to the host verifier (`deleg_tx`). -/
def evalJobSelective (t1s t1r t2s : Nat) (hostCheck : Bool) : TieredJobVerdict :=
  if t1s == 1 then
    { tier2Promoted := false, hostDelegated := false, accepted := true }
  else if t1s == 2 then
    { tier2Promoted := false, hostDelegated := false, accepted := false }
  else if isSelectiveTier2Promotable t1s t1r then
    if t2s == 1 then
      { tier2Promoted := true, hostDelegated := false, accepted := true }
    else if t2s == 2 then
      { tier2Promoted := true, hostDelegated := false, accepted := false }
    else
      { tier2Promoted := true, hostDelegated := true, accepted := hostCheck }
  else
    { tier2Promoted := false, hostDelegated := true, accepted := hostCheck }

/-- Batch accounting summary tracking the 4-way job partition under selective Tier-2 routing. -/
structure SelectiveBatchSummary where
  processed : Nat
  t1AccCount : Nat
  t1RejCount : Nat
  t2PromotedCount : Nat
  directHostCount : Nat
  t2AccCount : Nat
  t2RejCount : Nat
  t2HostCount : Nat
  acceptedCount : Nat
  rejectedCount : Nat
  allAccepted : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Sequential specification of evaluating jobs `0..n-1` under selective Tier-2 scheduling. -/
def runSelectiveBatch (t1Status t1Reason t2Status : Nat -> Nat) (hostCheck : Nat -> Bool) :
    Nat -> SelectiveBatchSummary
  | 0 =>
    { processed := 0
      t1AccCount := 0
      t1RejCount := 0
      t2PromotedCount := 0
      directHostCount := 0
      t2AccCount := 0
      t2RejCount := 0
      t2HostCount := 0
      acceptedCount := 0
      rejectedCount := 0
      allAccepted := true }
  | n + 1 =>
    let prev := runSelectiveBatch t1Status t1Reason t2Status hostCheck n
    let s1 := t1Status n
    let r1 := t1Reason n
    let s2 := t2Status n
    let v := evalJobSelective s1 r1 s2 (hostCheck n)
    let isT1Acc := s1 == 1
    let isT1Rej := !isT1Acc && (s1 == 2)
    let isT2 := !isT1Acc && !isT1Rej && isSelectiveTier2Promotable s1 r1
    let isDirect := !isT1Acc && !isT1Rej && !isT2
    let isT2Acc := isT2 && (s2 == 1)
    let isT2Rej := isT2 && !(s2 == 1) && (s2 == 2)
    let isT2Host := isT2 && !(s2 == 1) && !(s2 == 2)
    { processed := prev.processed + 1
      t1AccCount := prev.t1AccCount + if isT1Acc then 1 else 0
      t1RejCount := prev.t1RejCount + if isT1Rej then 1 else 0
      t2PromotedCount := prev.t2PromotedCount + if isT2 then 1 else 0
      directHostCount := prev.directHostCount + if isDirect then 1 else 0
      t2AccCount := prev.t2AccCount + if isT2Acc then 1 else 0
      t2RejCount := prev.t2RejCount + if isT2Rej then 1 else 0
      t2HostCount := prev.t2HostCount + if isT2Host then 1 else 0
      acceptedCount := prev.acceptedCount + if v.accepted then 1 else 0
      rejectedCount := prev.rejectedCount + if v.accepted then 0 else 1
      allAccepted := prev.allAccepted && v.accepted }

private theorem selective_beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hb : a == b
  · rfl
  · exact absurd (beq_iff_eq.mp hb) h

private theorem evalJobSelective_sound_single
    {t1s t1r t2s : Nat} {host isValid : Bool}
    (ht1Acc : t1s = 1 -> isValid = true)
    (ht1Rej : t1s = 2 -> isValid = false)
    (ht2Acc : t2s = 1 -> isValid = true)
    (ht2Rej : t2s = 2 -> isValid = false)
    (hhost : host = isValid) :
    (evalJobSelective t1s t1r t2s host).accepted = isValid ∧
    ((evalJobSelective t1s t1r t2s host).tier2Promoted = true ↔
      (t1s = 3 ∧ (t1r = reasonStackBudget ∨ t1r = reasonScratchBudget))) := by
  unfold evalJobSelective isSelectiveTier2Promotable
  refine ⟨?_, ?_⟩
  · by_cases h11 : t1s == 1
    · simp only [h11, ↓reduceIte]; exact (ht1Acc (beq_iff_eq.mp h11)).symm
    · simp only [h11, Bool.false_eq_true, ↓reduceIte]
      by_cases h12 : t1s == 2
      · simp only [h12, ↓reduceIte]; exact (ht1Rej (beq_iff_eq.mp h12)).symm
      · simp only [h12, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : ((t1s == 3) && (t1r == reasonStackBudget || t1r == reasonScratchBudget)) = true
        · simp only [hp, ↓reduceIte]
          by_cases h21 : t2s == 1
          · simp only [h21, ↓reduceIte]; exact (ht2Acc (beq_iff_eq.mp h21)).symm
          · simp only [h21, Bool.false_eq_true, ↓reduceIte]
            by_cases h22 : t2s == 2
            · simp only [h22, ↓reduceIte]; exact (ht2Rej (beq_iff_eq.mp h22)).symm
            · simp only [h22, Bool.false_eq_true, ↓reduceIte]; exact hhost
        · simp only [hp, Bool.false_eq_true, ↓reduceIte]; exact hhost
  · constructor
    · intro hprom
      by_cases h11 : t1s == 1
      · simp [h11] at hprom
      · by_cases h12 : t1s == 2
        · simp [h11, h12] at hprom
        · by_cases hp : ((t1s == 3) && (t1r == reasonStackBudget || t1r == reasonScratchBudget)) = true
          · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
            exact hp
          · simp [h11, h12, hp] at hprom
    · rintro ⟨hs, hr⟩
      have h11 : (t1s == 1) = false := by rw [hs]; rfl
      have h12 : (t1s == 2) = false := by rw [hs]; rfl
      have hp : ((t1s == 3) && (t1r == reasonStackBudget || t1r == reasonScratchBudget)) = true := by
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨hs, hr⟩
      simp only [h11, h12, Bool.false_eq_true, ↓reduceIte, hp]
      by_cases h21 : t2s == 1
      · simp [h21]
      · by_cases h22 : t2s == 2
        · simp [h21, h22]
        · simp [h21, h22]

/-- **Theorem (`selectiveTier2Promotion_sound`)**:
    Promoting ONLY `STATUS_DELEGATE` (`3`) jobs with `REASON_STACK_BUDGET` (`4`) or
    `REASON_SCRATCH_BUDGET` (`5`) to Tier 2 WGSL (`124` WGs), while delegating all other
    non-halted jobs directly to host verification, preserves total soundness
    (`hybridAccept = true ↔ ∀ i < n, isValid i = true`) and never masks `RejectedGpu`. -/
theorem selectiveTier2Promotion_sound
    (n : Nat) (t1Status t1Reason t2Status : Nat -> Nat)
    (hostCheck isValid : Nat -> Bool)
    (ht1Acc : ∀ i < n, t1Status i = 1 -> isValid i = true)
    (ht1Rej : ∀ i < n, t1Status i = 2 -> isValid i = false)
    (ht2Acc : ∀ i < n, t2Status i = 1 -> isValid i = true)
    (ht2Rej : ∀ i < n, t2Status i = 2 -> isValid i = false)
    (hhost : ∀ i < n, hostCheck i = isValid i) :
    let sum := runSelectiveBatch t1Status t1Reason t2Status hostCheck n
    (sum.allAccepted = true ↔ ∀ i < n, isValid i = true) ∧
    (∀ i < n, (evalJobSelective (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).accepted = isValid i) ∧
    (∀ i < n, (t1Status i = 2 ∨
      (isSelectiveTier2Promotable (t1Status i) (t1Reason i) = true ∧ t2Status i = 2)) ->
      (evalJobSelective (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).accepted = false ∧
      sum.allAccepted = false) ∧
    (∀ i < n, (evalJobSelective (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).tier2Promoted = true ↔
      (t1Status i = 3 ∧ (t1Reason i = 4 ∨ t1Reason i = 5))) := by
  induction n with
  | zero =>
    dsimp only [runSelectiveBatch]
    refine ⟨⟨(fun _ _ hi => absurd hi (Nat.not_lt_zero _)), (fun _ => rfl)⟩,
            (fun _ hi => absurd hi (Nat.not_lt_zero _)),
            (fun _ hi => absurd hi (Nat.not_lt_zero _)),
            (fun _ hi => absurd hi (Nat.not_lt_zero _))⟩
  | succ k ih =>
    have ih' := ih
      (fun i hi => ht1Acc i (Nat.lt_succ_of_lt hi))
      (fun i hi => ht1Rej i (Nat.lt_succ_of_lt hi))
      (fun i hi => ht2Acc i (Nat.lt_succ_of_lt hi))
      (fun i hi => ht2Rej i (Nat.lt_succ_of_lt hi))
      (fun i hi => hhost i (Nat.lt_succ_of_lt hi))
    dsimp only at ih'
    dsimp only [runSelectiveBatch]
    obtain ⟨hall, hev, hrej, hprom⟩ := ih'
    have hlast := @evalJobSelective_sound_single
      (t1Status k) (t1Reason k) (t2Status k) (hostCheck k) (isValid k)
      (ht1Acc k (Nat.lt_succ_self k))
      (ht1Rej k (Nat.lt_succ_self k))
      (ht2Acc k (Nat.lt_succ_self k))
      (ht2Rej k (Nat.lt_succ_self k))
      (hhost k (Nat.lt_succ_self k))
    refine ⟨?_, ?_, ?_, ?_⟩
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
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hev i hlt
      · exact hlast.1
    · intro i hi hbad
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · obtain ⟨hacc_i, hsum_k⟩ := hrej i hlt hbad
        refine ⟨hacc_i, ?_⟩
        simp [hsum_k]
      · have hval_i : isValid i = false := by
          rcases hbad with ht1 | ⟨hp, ht2⟩
          · exact ht1Rej i hi ht1
          · exact ht2Rej i hi ht2
        have hacc_i : (evalJobSelective (t1Status i) (t1Reason i) (t2Status i) (hostCheck i)).accepted = false := by
          rw [hlast.1]; exact hval_i
        refine ⟨hacc_i, ?_⟩
        rw [hacc_i]
        exact Bool.and_false _
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hprom i hlt
      · exact hlast.2

/-- **Theorem (`tier1StepCutoffDirectDelegate_sound`)**:
    Routing Tier-1 quantum cutoffs (`status = 0`, normalized to `(3, reasonStepBudget)`) and
    `REASON_STEP_BUDGET` (`3`) delegations directly to the host verifier (`deleg_tx`) skips
    Tier 2 completely (`tier2Promoted = false`), delegates to the host (`hostDelegated = true`),
    records status/reason `(3, 3)` cleanly, and matches `isValid` identically. -/
theorem tier1StepCutoffDirectDelegate_sound
    {t1s t1r t2s : Nat} {host isValid : Bool}
    (htrig : t1s = 0 ∨ (t1s = 3 ∧ t1r = reasonStepBudget))
    (hhost : host = isValid) :
    let v := evalJobSelective t1s t1r t2s host
    v.tier2Promoted = false ∧
    v.hostDelegated = true ∧
    v.accepted = isValid ∧
    normalizeDirectDelegateStatusReason t1s t1r = (3, reasonStepBudget) := by
  have h11 : (t1s == 1) = false := by
    rcases htrig with h0 | ⟨h3, _⟩
    · rw [h0]; rfl
    · rw [h3]; rfl
  have h12 : (t1s == 2) = false := by
    rcases htrig with h0 | ⟨h3, _⟩
    · rw [h0]; rfl
    · rw [h3]; rfl
  have hp : isSelectiveTier2Promotable t1s t1r = false := by
    dsimp only [isSelectiveTier2Promotable, reasonStackBudget, reasonScratchBudget]
    rcases htrig with h0 | ⟨h3, hr⟩
    · rw [h0]; rfl
    · rw [h3, hr]; rfl
  have hnorm : normalizeDirectDelegateStatusReason t1s t1r = (3, reasonStepBudget) := by
    unfold normalizeDirectDelegateStatusReason
    rcases htrig with h0 | ⟨h3, hr⟩
    · simp [h0]
    · simp [h3, hr]
  refine ⟨?_, ?_, ?_, hnorm⟩
  · unfold evalJobSelective; simp [h11, h12, hp]
  · unfold evalJobSelective; simp [h11, h12, hp]
  · unfold evalJobSelective; simp [h11, h12, hp, hhost]

/-- **Theorem (`hybridPartitionConservation`)**:
    Under Phase 6 selective Tier-2 scheduling over any `n` jobs, every job falls into
    exactly one of `{T1Accepted, T1Rejected, T2Promoted, DirectHostDelegated}`,
    every Tier-2 promoted job resolves into `{T2Accepted, T2Rejected, T2HostDelegated}`,
    and exact acceptance/rejection conservation holds (`acceptedCount + rejectedCount = n`). -/
theorem hybridPartitionConservation
    (n : Nat) (t1Status t1Reason t2Status : Nat -> Nat) (hostCheck : Nat -> Bool) :
    let sum := runSelectiveBatch t1Status t1Reason t2Status hostCheck n
    sum.processed = n ∧
    sum.t1AccCount + sum.t1RejCount + sum.t2PromotedCount + sum.directHostCount = n ∧
    sum.t2AccCount + sum.t2RejCount + sum.t2HostCount = sum.t2PromotedCount ∧
    sum.acceptedCount + sum.rejectedCount = n := by
  induction n with
  | zero => simp [runSelectiveBatch]
  | succ k ih =>
    dsimp only [runSelectiveBatch] at ih ⊢
    obtain ⟨hp, hpart, ht2, hacc⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hp]
    · by_cases h1 : (t1Status k == 1) = true
      · simp [h1]; omega
      · have h1f : (t1Status k == 1) = false := Bool.eq_false_iff.mpr h1
        by_cases h2 : (t1Status k == 2) = true
        · simp [h1f, h2]; omega
        · have h2f : (t1Status k == 2) = false := Bool.eq_false_iff.mpr h2
          by_cases h3 : isSelectiveTier2Promotable (t1Status k) (t1Reason k) = true
          · simp [h1f, h2f, h3]; omega
          · have h3f : isSelectiveTier2Promotable (t1Status k) (t1Reason k) = false :=
              Bool.eq_false_iff.mpr h3
            simp [h1f, h2f, h3f]; omega
    · by_cases h1 : (t1Status k == 1) = true
      · simp [h1]; exact ht2
      · have h1f : (t1Status k == 1) = false := Bool.eq_false_iff.mpr h1
        by_cases h2 : (t1Status k == 2) = true
        · simp [h1f, h2]; exact ht2
        · have h2f : (t1Status k == 2) = false := Bool.eq_false_iff.mpr h2
          by_cases h3 : isSelectiveTier2Promotable (t1Status k) (t1Reason k) = true
          · by_cases hs21 : (t2Status k == 1) = true
            · simp [h1f, h2f, h3, hs21]; omega
            · have hs21f : (t2Status k == 1) = false := Bool.eq_false_iff.mpr hs21
              by_cases hs22 : (t2Status k == 2) = true
              · simp [h1f, h2f, h3, hs21f, hs22]; omega
              · have hs22f : (t2Status k == 2) = false := Bool.eq_false_iff.mpr hs22
                simp [h1f, h2f, h3, hs21f, hs22f]; omega
          · have h3f : isSelectiveTier2Promotable (t1Status k) (t1Reason k) = false :=
              Bool.eq_false_iff.mpr h3
            simp [h1f, h2f, h3f]; exact ht2
    · cases (evalJobSelective (t1Status k) (t1Reason k) (t2Status k) (hostCheck k)).accepted <;>
        simp <;> omega


/-! ### 2. Vulkan Binding & Occupancy Arithmetic -/

/-- Phase 6 Tier-2 workgroup count (`124` WGs * `64` lanes * `65_536` scratch `u32` words). -/
def tier2MaxWgsPhase6 : Nat := 124
def wgSizePhase6 : Nat := 64
def tier2MaxScratchWordsPhase6 : Nat := 65536
def tier2MaxStepsPhase6 : Nat := 131072
def vulkanMaxBindingSafe : Nat := 2147483644

/-- **Theorem (`tier2Wgs124FitsVulkan`)**:
    Tier-2 scratch allocation at `124` workgroups (`124 * 64 * 65536 * 4 = 2080374784` bytes)
    fits strictly inside the Vulkan storage-buffer binding ceiling `2147483644` bytes (`< 2^31`). -/
theorem tier2Wgs124FitsVulkan :
    124 * 64 * 65536 * 4 ≤ 2147483644 ∧
    tier2MaxWgsPhase6 * wgSizePhase6 * tier2MaxScratchWordsPhase6 * 4 = 2080374784 ∧
    tier2MaxWgsPhase6 * wgSizePhase6 * tier2MaxScratchWordsPhase6 * 4 < 2 ^ 31 := by
  decide

/-- Start word index of lane `lane` with per-lane word stride `scratchWords`. -/
def laneScratchStart (lane scratchWords : Nat) : Nat := lane * scratchWords

/-- Exclusive end word index of lane `lane` with per-lane word stride `scratchWords`. -/
def laneScratchEnd (lane scratchWords : Nat) : Nat := (lane + 1) * scratchWords

/-- **Theorem (`tier1BindingClamp_sound`)**:
    Clamping active workgroups by `maxBindingBytes / (wgSize * scratchWords * 4)` guarantees
    that the total byte footprint stays `≤ maxBindingBytes`, every lane word offset fits inside
    the bound buffer, and distinct lanes `[l * scratchWords, (l + 1) * scratchWords)` are
    pairwise disjoint. -/
theorem tier1BindingClamp_sound
    (maxBindingBytes wgSize scratchWords activeWgs : Nat)
    (hwg : 0 < wgSize) (hsw : 0 < scratchWords)
    (hclamp : activeWgs ≤ maxBindingBytes / (wgSize * scratchWords * 4)) :
    activeWgs * wgSize * scratchWords * 4 ≤ maxBindingBytes ∧
    (∀ lane off, lane < activeWgs * wgSize -> off < scratchWords ->
      (laneScratchStart lane scratchWords + off + 1) * 4 ≤ maxBindingBytes) ∧
    (∀ l1 l2, l1 ≠ l2 ->
      laneScratchEnd l1 scratchWords ≤ laneScratchStart l2 scratchWords ∨
      laneScratchEnd l2 scratchWords ≤ laneScratchStart l1 scratchWords) := by
  have hstridePos : 0 < wgSize * scratchWords * 4 :=
    Nat.mul_pos (Nat.mul_pos hwg hsw) (by decide)
  have hbytes : activeWgs * wgSize * scratchWords * 4 ≤ maxBindingBytes := by
    have hmul := Nat.mul_le_mul_right (wgSize * scratchWords * 4) hclamp
    have hdiv : (maxBindingBytes / (wgSize * scratchWords * 4)) * (wgSize * scratchWords * 4) ≤
        maxBindingBytes := Nat.div_mul_le_self maxBindingBytes (wgSize * scratchWords * 4)
    have hle := Nat.le_trans hmul hdiv
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at hle
    exact hle
  refine ⟨hbytes, ?_, ?_⟩
  · intro lane off hlane hoff
    have h1 : laneScratchStart lane scratchWords + off + 1 ≤ (lane + 1) * scratchWords := by
      unfold laneScratchStart
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : (lane + 1) * scratchWords ≤ activeWgs * wgSize * scratchWords :=
      Nat.mul_le_mul_right scratchWords hlane
    have h3 : (laneScratchStart lane scratchWords + off + 1) * 4 ≤
        activeWgs * wgSize * scratchWords * 4 :=
      Nat.mul_le_mul_right 4 (Nat.le_trans h1 h2)
    exact Nat.le_trans h3 hbytes
  · intro l1 l2 hne
    unfold laneScratchStart laneScratchEnd
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · left; exact Nat.mul_le_mul_right scratchWords hlt
    · right; exact Nat.mul_le_mul_right scratchWords hlt

/-- **Theorem (`adaptiveScratchClamping_sound`)**:
    When `wgSize * wgStrideWords * 4 ≤ maxBindingBytes` and `scratchWords ≤ wgStrideWords`
    (modeling `wgStrideWords = maxStackFrames * 8 + scratchWords`), clamping `actualWgs` by
    `min tierMaxWgs (max (maxBindingBytes / (wgSize * wgStrideWords * 4)) 1)` keeps both
    `actualWgs ≤ tierMaxWgs` and total bytes `≤ maxBindingBytes`, while giving every lane
    an in-bounds, pairwise-disjoint scratch region of `scratchWords` words. -/
theorem adaptiveScratchClamping_sound
    (maxBindingBytes tierMaxWgs wgSize wgStrideWords scratchWords actualWgs : Nat)
    (hwg : 0 < wgSize) (hstr : 0 < wgStrideWords) (_hsw : 0 < scratchWords)
    (hscr : scratchWords ≤ wgStrideWords)
    (hfit : wgSize * wgStrideWords * 4 ≤ maxBindingBytes)
    (hactual : actualWgs ≤ min tierMaxWgs (max (maxBindingBytes / (wgSize * wgStrideWords * 4)) 1)) :
    1 ≤ maxBindingBytes / (wgSize * wgStrideWords * 4) ∧
    actualWgs ≤ tierMaxWgs ∧
    actualWgs * wgSize * wgStrideWords * 4 ≤ maxBindingBytes ∧
    (∀ lane off, lane < actualWgs * wgSize -> off < scratchWords ->
      (laneScratchStart lane wgStrideWords + off + 1) * 4 ≤ maxBindingBytes) ∧
    (∀ l1 l2, l1 ≠ l2 ->
      laneScratchStart l1 wgStrideWords + scratchWords ≤ laneScratchStart l2 wgStrideWords ∨
      laneScratchStart l2 wgStrideWords + scratchWords ≤ laneScratchStart l1 wgStrideWords) := by
  have hstridePos : 0 < wgSize * wgStrideWords * 4 :=
    Nat.mul_pos (Nat.mul_pos hwg hstr) (by decide)
  have hge1 : 1 ≤ maxBindingBytes / (wgSize * wgStrideWords * 4) := by
    rw [Nat.le_div_iff_mul_le hstridePos, Nat.one_mul]
    exact hfit
  have hmaxEq : max (maxBindingBytes / (wgSize * wgStrideWords * 4)) 1 =
      maxBindingBytes / (wgSize * wgStrideWords * 4) := Nat.max_eq_left hge1
  have hleMin := hactual
  rw [hmaxEq] at hleMin
  have htier : actualWgs ≤ tierMaxWgs := Nat.le_trans hleMin (Nat.min_le_left _ _)
  have hlim : actualWgs ≤ maxBindingBytes / (wgSize * wgStrideWords * 4) :=
    Nat.le_trans hleMin (Nat.min_le_right _ _)
  have hbind := tier1BindingClamp_sound maxBindingBytes wgSize wgStrideWords actualWgs hwg hstr hlim
  refine ⟨hge1, htier, hbind.1, ?_, ?_⟩
  · intro lane off hlane hoff
    exact hbind.2.1 lane off hlane (Nat.lt_of_lt_of_le hoff hscr)
  · intro l1 l2 hne
    rcases hbind.2.2 l1 l2 hne with h12 | h21
    · left
      have hle : laneScratchStart l1 wgStrideWords + scratchWords ≤
          laneScratchEnd l1 wgStrideWords := by
        unfold laneScratchStart laneScratchEnd
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left hscr _
      exact Nat.le_trans hle h12
    · right
      have hle : laneScratchStart l2 wgStrideWords + scratchWords ≤
          laneScratchEnd l2 wgStrideWords := by
        unfold laneScratchStart laneScratchEnd
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left hscr _
      exact Nat.le_trans hle h21


/-! ### 3. Parallel Columnar Decode & Frozen `ConsMap` Order Determinism -/

/-- Extracts the `O(1)` byte slice `[off, off + len)` from `bytes`. -/
def sliceList {α : Type u} (bytes : List α) (off len : Nat) : List α :=
  (bytes.drop off).take len

/-- Sequential `ColReader` validation & slicing over `HostSection` tables of lengths `lens`. -/
def sliceTablesFrom {α : Type u} (bytes : List α) (off : Nat) : List Nat -> Option (List (List α))
  | [] => some []
  | len :: rest =>
    if off + len ≤ bytes.length then
      match sliceTablesFrom bytes (off + len) rest with
      | some tail => some (sliceList bytes off len :: tail)
      | none => none
    else
      none

/-- Precomputed `(offset, len)` byte spans for parallel decoding of `HostSection` tables. -/
def tableSpans (off : Nat) : List Nat -> List (Nat × Nat)
  | [] => []
  | len :: rest => (off, len) :: tableSpans (off + len) rest

/-- Two spans `[o1, o1 + l1)` and `[o2, o2 + l2)` are byte-interval disjoint. -/
def spansDisjoint (s1 s2 : Nat × Nat) : Prop :=
  s1.1 + s1.2 ≤ s2.1 ∨ s2.1 + s2.2 ≤ s1.1

private theorem tableSpans_start_ge {off : Nat} {lens : List Nat} {s : Nat × Nat}
    (hs : s ∈ tableSpans off lens) : off ≤ s.1 := by
  induction lens generalizing off with
  | nil => simp [tableSpans] at hs
  | cons len rest ih =>
    unfold tableSpans at hs
    rcases List.mem_cons.mp hs with rfl | htail
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_add_right off len) (ih htail)

private theorem tableSpans_in_bounds {α : Type u} {bytes : List α} {off : Nat} {lens : List Nat}
    {slices : List (List α)} (hseq : sliceTablesFrom bytes off lens = some slices)
    {s : Nat × Nat} (hs : s ∈ tableSpans off lens) :
    s.1 + s.2 ≤ bytes.length := by
  induction lens generalizing off slices with
  | nil => simp [tableSpans] at hs
  | cons len rest ih =>
    unfold sliceTablesFrom at hseq
    split at hseq
    · next hfit =>
      cases htail : sliceTablesFrom bytes (off + len) rest with
      | none => rw [htail] at hseq; cases hseq
      | some restSlices =>
        unfold tableSpans at hs
        rcases List.mem_cons.mp hs with rfl | hmem
        · exact hfit
        · exact ih htail hmem
    · cases hseq

private theorem tableSpans_pairwise_disjoint (off : Nat) (lens : List Nat) :
    (tableSpans off lens).Pairwise spansDisjoint := by
  induction lens generalizing off with
  | nil => exact List.Pairwise.nil
  | cons len rest ih =>
    unfold tableSpans
    refine List.Pairwise.cons ?_ (ih (off + len))
    intro s hs
    left
    exact tableSpans_start_ge hs

/-- Fixed-stride `par_chunks` helper splitting a contiguous table slice into chunks of `stride`
    elements each (e.g., row chunks of `~60M` `apps.rows`). -/
def splitFixedChunks {α : Type u} (stride chunkRows : Nat) : List α -> List (List α)
  | [] => []
  | b :: bs =>
    if stride = 0 ∨ chunkRows = 0 then [b :: bs]
    else
      let step := chunkRows * stride
      (b :: bs).take step :: splitFixedChunks stride chunkRows ((b :: bs).drop step)
termination_by bytes => bytes.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  rename_i hne
  have h1 : stride ≠ 0 := fun hz => hne (Or.inl hz)
  have h2 : chunkRows ≠ 0 := fun hz => hne (Or.inr hz)
  have hpos : 0 < chunkRows * stride := Nat.mul_pos (Nat.pos_of_ne_zero h2) (Nat.pos_of_ne_zero h1)
  omega

/-- Decodes fixed-stride `rowSize`-byte rows sequentially (e.g. `Apps`/`Foralls`/`Lams` rows). -/
def decodeRowsSeq {α : Type u} {ρ : Type v} (rowSize : Nat) (decRow : List α -> ρ) :
    List α -> List ρ
  | [] => []
  | b :: bs =>
    if rowSize = 0 then []
    else decRow ((b :: bs).take rowSize) :: decodeRowsSeq rowSize decRow ((b :: bs).drop rowSize)
termination_by bytes => bytes.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  rename_i hnz
  have hpos : 0 < rowSize := Nat.pos_of_ne_zero hnz
  omega

private theorem splitFixedChunks_cons {α : Type u} (stride chunkRows : Nat)
    (hstr : 0 < stride) (hchk : 0 < chunkRows) (b : α) (bs : List α) :
    splitFixedChunks stride chunkRows (b :: bs) =
      (b :: bs).take (chunkRows * stride) ::
        splitFixedChunks stride chunkRows ((b :: bs).drop (chunkRows * stride)) := by
  rw [splitFixedChunks.eq_2]
  have h1 : stride ≠ 0 := Nat.ne_of_gt hstr
  have h2 : chunkRows ≠ 0 := Nat.ne_of_gt hchk
  simp [h1, h2]

private theorem decodeRowsSeq_cons {α : Type u} {ρ : Type v} (rowSize : Nat)
    (hrow : 0 < rowSize) (decRow : List α -> ρ) (b : α) (bs : List α) :
    decodeRowsSeq rowSize decRow (b :: bs) =
      decRow ((b :: bs).take rowSize) :: decodeRowsSeq rowSize decRow ((b :: bs).drop rowSize) := by
  rw [decodeRowsSeq.eq_2]
  have hnz : rowSize ≠ 0 := Nat.ne_of_gt hrow
  simp [hnz]

private theorem take_take_min {α : Type u} (a b : Nat) (xs : List α) :
    (xs.take a).take b = xs.take (min a b) := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | zero => simp
    | succ a =>
      cases b with
      | zero => simp
      | succ b =>
        simp [Nat.succ_min_succ, ih]

private theorem decodeRowsSeq_take_mul {α : Type u} {ρ : Type v}
    (rowSize k : Nat) (hrow : 0 < rowSize) (decRow : List α -> ρ) (bytes : List α) :
    decodeRowsSeq rowSize decRow bytes =
      decodeRowsSeq rowSize decRow (bytes.take (k * rowSize)) ++
      decodeRowsSeq rowSize decRow (bytes.drop (k * rowSize)) := by
  induction k generalizing bytes with
  | zero =>
    rw [Nat.zero_mul, List.take_zero, List.drop_zero, decodeRowsSeq.eq_1, List.nil_append]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [Nat.zero_add, Nat.one_mul]
      cases bytes with
      | nil =>
        rw [List.take_nil, List.drop_nil, decodeRowsSeq.eq_1, List.nil_append]
      | cons b bs =>
        have h1 := decodeRowsSeq_cons rowSize hrow decRow b bs
        have htake_ne : ((b :: bs).take rowSize) ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp only [List.length_take, List.length_cons, List.length_nil] at this
          omega
        cases ht : (b :: bs).take rowSize with
        | nil => exact absurd ht htake_ne
        | cons t ts =>
          have h2 := decodeRowsSeq_cons rowSize hrow decRow t ts
          have hdrop_nil : (t :: ts).drop rowSize = [] := by
            rw [← ht, List.drop_eq_nil_iff, List.length_take]
            exact Nat.min_le_left _ _
          have htake_eq : (t :: ts).take rowSize = (b :: bs).take rowSize := by
            rw [← ht, take_take_min, Nat.min_self]
          rw [h1, h2, htake_eq, hdrop_nil, decodeRowsSeq.eq_1]
          rfl
    | succ k =>
      cases bytes with
      | nil =>
        rw [List.take_nil, List.drop_nil, decodeRowsSeq.eq_1, List.nil_append]
      | cons b bs =>
        have hdrop_take : ((b :: bs).take ((k + 2) * rowSize)).drop rowSize =
            ((b :: bs).drop rowSize).take ((k + 1) * rowSize) := by
          rw [List.drop_take]
          have hmul : (k + 2) * rowSize - rowSize = (k + 1) * rowSize := by
            rw [Nat.succ_mul]; omega
          rw [hmul]
        have hdrop_drop : ((b :: bs).drop rowSize).drop ((k + 1) * rowSize) =
            (b :: bs).drop ((k + 2) * rowSize) := by
          rw [List.drop_drop, Nat.add_comm rowSize ((k + 1) * rowSize)]
          have hmul : (k + 1) * rowSize + rowSize = (k + 2) * rowSize :=
            (Nat.succ_mul (k + 1) rowSize).symm
          rw [hmul]
        have hlen_take : ((b :: bs).take ((k + 2) * rowSize)) ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp only [List.length_take, List.length_cons, List.length_nil] at this
          have : 0 < (k + 2) * rowSize := Nat.mul_pos (Nat.succ_pos _) hrow
          omega
        cases ht : (b :: bs).take ((k + 2) * rowSize) with
        | nil => exact absurd ht hlen_take
        | cons t ts =>
          have hleft := decodeRowsSeq_cons rowSize hrow decRow b bs
          have htake_head : (t :: ts).take rowSize = (b :: bs).take rowSize := by
            rw [← ht, take_take_min]
            have hle : rowSize ≤ (k + 2) * rowSize := Nat.le_mul_of_pos_left rowSize (Nat.succ_pos _)
            rw [Nat.min_eq_right hle]
          have hrt := decodeRowsSeq_cons rowSize hrow decRow t ts
          have htdrop : (t :: ts).drop rowSize = ((b :: bs).drop rowSize).take ((k + 1) * rowSize) := by
            rw [← ht, hdrop_take]
          rw [hleft, hrt, htake_head, htdrop, ih ((b :: bs).drop rowSize), hdrop_drop]
          rfl

private theorem decodeRowsSeq_chunked_aux {α : Type u} {ρ : Type v}
    (n rowSize chunkRows : Nat) (hrow : 0 < rowSize) (hchk : 0 < chunkRows)
    (decRow : List α -> ρ) (bytes : List α) (hlen : bytes.length ≤ n) :
    ((splitFixedChunks rowSize chunkRows bytes).map (decodeRowsSeq rowSize decRow)).flatten =
      decodeRowsSeq rowSize decRow bytes := by
  induction n generalizing bytes with
  | zero =>
    have hnil : bytes = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hnil
    rw [splitFixedChunks.eq_1, decodeRowsSeq.eq_1]
    rfl
  | succ n ih =>
    cases bytes with
    | nil =>
      rw [splitFixedChunks.eq_1, decodeRowsSeq.eq_1]
      rfl
    | cons b bs =>
      have hunf := splitFixedChunks_cons rowSize chunkRows hrow hchk b bs
      have hdrop_len : ((b :: bs).drop (chunkRows * rowSize)).length ≤ n := by
        have hpos : 0 < chunkRows * rowSize := Nat.mul_pos hchk hrow
        simp only [List.length_drop, List.length_cons] at hlen ⊢
        omega
      rw [hunf, List.map_cons, List.flatten_cons]
      rw [ih ((b :: bs).drop (chunkRows * rowSize)) hdrop_len]
      rw [← decodeRowsSeq_take_mul rowSize chunkRows hrow decRow (b :: bs)]

/-- **Theorem (`parallelColDecode_exact`)**:
    Precomputing disjoint `HostSection` `(offset, len)` byte spans once in `O(1)` per table
    and decoding each table slice independently in parallel (plus chunking fixed-stride row
    tables via `splitFixedChunks` / `par_chunks`) produces pairwise-disjoint in-bounds slices
    and decodes identically to sequential cursor decoding. -/
theorem parallelColDecode_exact {α : Type u} {β : Type v} {ρ : Type w}
    (bytes : List α) (lens : List Nat) (decodeTable : List α -> β)
    (slices : List (List α))
    (hseq : sliceTablesFrom bytes 0 lens = some slices)
    (rowSize chunkRows : Nat) (hrow : 0 < rowSize) (hchk : 0 < chunkRows)
    (decRow : List α -> ρ) (rowBytes : List α) :
    (tableSpans 0 lens).Pairwise spansDisjoint ∧
    (∀ s ∈ tableSpans 0 lens, s.1 + s.2 ≤ bytes.length) ∧
    (tableSpans 0 lens).map (fun s => decodeTable (sliceList bytes s.1 s.2)) =
      slices.map decodeTable ∧
    ((splitFixedChunks rowSize chunkRows rowBytes).map (decodeRowsSeq rowSize decRow)).flatten =
      decodeRowsSeq rowSize decRow rowBytes := by
  refine ⟨tableSpans_pairwise_disjoint 0 lens,
          (fun s hs => tableSpans_in_bounds hseq hs), ?_, ?_⟩
  · have hgen : ∀ (off : Nat) (ls : List Nat) (sls : List (List α)),
        sliceTablesFrom bytes off ls = some sls ->
        (tableSpans off ls).map (fun s => decodeTable (sliceList bytes s.1 s.2)) =
          sls.map decodeTable := by
      intro off ls
      induction ls generalizing off with
      | nil =>
        intro sls h
        unfold sliceTablesFrom at h
        injection h with heq
        subst heq; rfl
      | cons l rest ih =>
        intro sls h
        unfold sliceTablesFrom at h
        split at h
        · cases htail : sliceTablesFrom bytes (off + l) rest with
          | none => rw [htail] at h; cases h
          | some restSls =>
            rw [htail] at h
            injection h with heq
            subst heq
            unfold tableSpans
            simp only [List.map_cons]
            congr 1
            exact ih (off + l) restSls htail
        · cases h
    exact hgen 0 lens slices hseq
  · exact decodeRowsSeq_chunked_aux rowBytes.length rowSize chunkRows hrow hchk decRow rowBytes (Nat.le_refl _)


/-- Lookup in an association-style `ConsMap` representation (`List (κ × ν)`). -/
def consLookup {κ : Type u} {ν : Type v} [DecidableEq κ] : List (κ × ν) -> κ -> Option ν
  | [], _ => none
  | (k', v) :: rest, k => if k' = k then some v else consLookup rest k

/-- Insert-if-absent into a `ConsMap`, matching frozen unique-row index insertion. -/
def insertUniqueCons {κ : Type u} {ν : Type v} [DecidableEq κ]
    (m : List (κ × ν)) (kv : κ × ν) : List (κ × ν) :=
  match consLookup m kv.1 with
  | some _ => m
  | none => kv :: m

/-- Key uniqueness predicate for canonical deduplicated `HostSection` tables. -/
def NodupKeys {κ : Type u} {ν : Type v} (rows : List (κ × ν)) : Prop :=
  rows.Pairwise (fun a b => a.1 ≠ b.1)

/-- Sequential `ConsMap` rebuild (`foldl`) over a slice of canonical table rows. -/
def buildConsMapSeq {κ : Type u} {ν : Type v} [DecidableEq κ]
    (rows : List (κ × ν)) : List (κ × ν) :=
  rows.foldl insertUniqueCons []

/-- Disjoint shard merge combining two independently built `ConsMap` shards. -/
def mergeConsShards {κ : Type u} {ν : Type v} [DecidableEq κ]
    (leftMap rightMap : List (κ × ν)) : List (κ × ν) :=
  leftMap.foldl insertUniqueCons rightMap

private theorem consLookup_insertUniqueCons {κ : Type u} {ν : Type v} [DecidableEq κ]
    (m : List (κ × ν)) (kv : κ × ν) (k : κ) :
    consLookup (insertUniqueCons m kv) k =
      match consLookup m kv.1 with
      | some _ => consLookup m k
      | none => if kv.1 = k then some kv.2 else consLookup m k := by
  unfold insertUniqueCons
  cases h : consLookup m kv.1 with
  | some v => rfl
  | none => rfl

private theorem consLookup_foldl_none {κ : Type u} {ν : Type v} [DecidableEq κ]
    (rows : List (κ × ν)) (m : List (κ × ν)) (k : κ)
    (hm : consLookup m k = none) (habsent : ∀ v, (k, v) ∉ rows) :
    consLookup (rows.foldl insertUniqueCons m) k = none := by
  induction rows generalizing m with
  | nil => exact hm
  | cons kv rest ih =>
    simp only [List.foldl_cons]
    refine ih (insertUniqueCons m kv) ?_ (fun v hmem => habsent v (List.mem_cons_of_mem kv hmem))
    rw [consLookup_insertUniqueCons]
    cases h : consLookup m kv.1 with
    | some _ => exact hm
    | none =>
      by_cases heq : kv.1 = k
      · exfalso
        have hp : kv = (k, kv.2) := by
          cases kv; simp only at heq; subst heq; rfl
        exact habsent kv.2 (hp ▸ List.mem_cons_self)
      · simp [heq, hm]

private theorem consLookup_foldl_some_of_mem {κ : Type u} {ν : Type v} [DecidableEq κ]
    (m : List (κ × ν)) {k : κ} {v : ν} (hm : consLookup m k = some v)
    (rows : List (κ × ν)) :
    consLookup (rows.foldl insertUniqueCons m) k = some v := by
  induction rows generalizing m with
  | nil => exact hm
  | cons kv rest ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [consLookup_insertUniqueCons]
    cases h : consLookup m kv.1 with
    | some _ => exact hm
    | none =>
      by_cases heq : kv.1 = k
      · rw [heq, hm] at h; cases h
      · simp [heq, hm]

private theorem nodupKeys_mem_unique {κ : Type u} {ν : Type v}
    {rows : List (κ × ν)} (hn : NodupKeys rows) {k : κ} {v1 v2 : ν}
    (h1 : (k, v1) ∈ rows) (h2 : (k, v2) ∈ rows) : v1 = v2 := by
  induction rows with
  | nil => cases h1
  | cons kv rest ih =>
    rcases hn with _ | ⟨hhead, htail⟩
    rcases List.mem_cons.mp h1 with h1e | h1t <;> rcases List.mem_cons.mp h2 with h2e | h2t
    · rw [← h1e] at h2e; cases h2e; rfl
    · subst h1e; exact absurd rfl (hhead (k, v2) h2t)
    · subst h2e; exact absurd rfl (hhead (k, v1) h1t)
    · exact ih htail h1t h2t

private theorem consLookup_foldl_nodup {κ : Type u} {ν : Type v} [DecidableEq κ]
    (rows : List (κ × ν)) (m : List (κ × ν))
    (hn : NodupKeys rows)
    (hmDisj : ∀ a ∈ m, ∀ b ∈ rows, a.1 ≠ b.1)
    (k : κ) :
    (∀ v, (k, v) ∈ rows -> consLookup (rows.foldl insertUniqueCons m) k = some v) ∧
    ((∀ v, (k, v) ∉ rows) -> consLookup (rows.foldl insertUniqueCons m) k = consLookup m k) := by
  induction rows generalizing m with
  | nil =>
    exact ⟨(fun _ h => by cases h), (fun _ => rfl)⟩
  | cons kv rest ih =>
    rcases hn with _ | ⟨hhead, htail⟩
    have hm_kv : consLookup m kv.1 = none := by
      clear ih
      induction m with
      | nil => rfl
      | cons a m' ihm =>
        unfold consLookup
        have hne : a.1 ≠ kv.1 := hmDisj a (List.mem_cons_self) kv (List.mem_cons_self)
        simp only [hne, ↓reduceIte]
        exact ihm (fun x hx b hb => hmDisj x (List.mem_cons_of_mem a hx) b hb)
    have hdisj' : ∀ a ∈ insertUniqueCons m kv, ∀ b ∈ rest, a.1 ≠ b.1 := by
      unfold insertUniqueCons
      rw [hm_kv]
      intro a ha b hb
      rcases List.mem_cons.mp ha with rfl | ham
      · exact hhead b hb
      · exact hmDisj a ham b (List.mem_cons_of_mem kv hb)
    have ih' := ih (insertUniqueCons m kv) htail hdisj'
    refine ⟨?_, ?_⟩
    · intro v hmem
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hrest
      · apply consLookup_foldl_some_of_mem
        rw [consLookup_insertUniqueCons, hm_kv]
        simp
      · exact ih'.1 v hrest
    · intro habs
      simp only [List.foldl_cons]
      rw [ih'.2 (fun v hv => habs v (List.mem_cons_of_mem kv hv))]
      rw [consLookup_insertUniqueCons, hm_kv]
      have hne : kv.1 ≠ k := by
        intro heq
        have hp : kv = (k, kv.2) := by cases kv; simp only at heq; subst heq; rfl
        exact habs kv.2 (hp ▸ List.mem_cons_self)
      simp [hne]

private theorem consLookup_build_nodup {κ : Type u} {ν : Type v} [DecidableEq κ]
    {rows : List (κ × ν)} (hn : NodupKeys rows) (k : κ) (v : ν) :
    consLookup (buildConsMapSeq rows) k = some v ↔ (k, v) ∈ rows := by
  have h := consLookup_foldl_nodup rows [] hn (fun _ ha => by cases ha) k
  constructor
  · intro hlook
    by_cases hex : ∃ w, (k, w) ∈ rows
    · obtain ⟨w, hw⟩ := hex
      have h1 := h.1 w hw
      unfold buildConsMapSeq at hlook
      rw [hlook] at h1
      injection h1 with heq
      rw [heq]; exact hw
    · have habs : ∀ w, (k, w) ∉ rows := fun w hw => hex ⟨w, hw⟩
      have hnone := h.2 habs
      change consLookup (buildConsMapSeq rows) k = consLookup [] k at hnone
      rw [hlook] at hnone
      cases hnone
  · intro hmem
    unfold buildConsMapSeq
    exact h.1 v hmem

private theorem foldl_append {α : Type u} {β : Type v} (f : β -> α -> β) (acc : β) (l1 l2 : List α) :
    (l1 ++ l2).foldl f acc = l2.foldl f (l1.foldl f acc) :=
  List.foldl_append

/-- **Theorem (`uniqueRowConsInsert_exact`)**:
    When a frozen `HostSection` table `rows` has duplicate-free keys (`NodupKeys rows`):
    1. `consLookup (buildConsMapSeq rows) k = some v ↔ (k, v) ∈ rows`.
    2. **Order & Shard Determinism**: ANY two duplicate-free reorderings/shards (`rows1`, `rows2`)
       with identical row membership produce the exact same lookup table `∀ k, consLookup ...`.
    3. Merging disjoint left/right `ConsMap` shards (`mergeConsShards`) preserves exact lookup
       equivalence with sequential `buildConsMapSeq (left ++ right)`. -/
theorem uniqueRowConsInsert_exact {κ : Type u} {ν : Type v} [DecidableEq κ]
    (rows1 rows2 : List (κ × ν))
    (hn1 : NodupKeys rows1) (hn2 : NodupKeys rows2)
    (hequiv : ∀ p, p ∈ rows1 ↔ p ∈ rows2)
    (left right : List (κ × ν))
    (hnSplit : NodupKeys (left ++ right)) :
    (∀ k v, consLookup (buildConsMapSeq rows1) k = some v ↔ (k, v) ∈ rows1) ∧
    (∀ k, consLookup (buildConsMapSeq rows1) k = consLookup (buildConsMapSeq rows2) k) ∧
    (∀ k, consLookup (mergeConsShards left (buildConsMapSeq right)) k =
          consLookup (buildConsMapSeq (left ++ right)) k) := by
  refine ⟨(fun k v => consLookup_build_nodup hn1 k v), ?_, ?_⟩
  · intro k
    cases h1 : consLookup (buildConsMapSeq rows1) k with
    | none =>
      symm
      cases h2 : consLookup (buildConsMapSeq rows2) k with
      | none => rfl
      | some v =>
        have hm2 : (k, v) ∈ rows2 := (consLookup_build_nodup hn2 k v).mp h2
        have hm1 : (k, v) ∈ rows1 := (hequiv (k, v)).mpr hm2
        have h1' := (consLookup_build_nodup hn1 k v).mpr hm1
        rw [h1] at h1'; cases h1'
    | some v =>
      have hm1 : (k, v) ∈ rows1 := (consLookup_build_nodup hn1 k v).mp h1
      have hm2 : (k, v) ∈ rows2 := (hequiv (k, v)).mp hm1
      exact ((consLookup_build_nodup hn2 k v).mpr hm2).symm
  · intro k
    have hnParts := List.pairwise_append.mp hnSplit
    have hnLeft : NodupKeys left := hnParts.1
    have hnRight : NodupKeys right := hnParts.2.1
    have hdisj : ∀ a ∈ left, ∀ b ∈ right, a.1 ≠ b.1 := hnParts.2.2
    have hshardDisj : ∀ a ∈ buildConsMapSeq right, ∀ b ∈ left, a.1 ≠ b.1 := by
      intro a ha b hb heq
      have hmemA : (a.1, a.2) ∈ right := by
        clear hdisj
        unfold buildConsMapSeq at ha
        suffices ∀ (xs acc : List (κ × ν)),
            (∀ x ∈ acc, x ∈ right) -> (∀ x ∈ xs, x ∈ right) ->
            a ∈ xs.foldl insertUniqueCons acc -> a ∈ right from
          this right [] (fun _ h => by cases h) (fun _ h => h) ha
        intro xs acc hacc hxs ha'
        induction xs generalizing acc with
        | nil => exact hacc a ha'
        | cons x xs ih =>
          apply ih (insertUniqueCons acc x)
          · intro y hy
            unfold insertUniqueCons at hy
            split at hy
            · exact hacc y hy
            · rcases List.mem_cons.mp hy with hyx | hy'
              · rw [hyx]; exact hxs x (List.mem_cons_self)
              · exact hacc y hy'
          · intro y hy; exact hxs y (List.mem_cons_of_mem x hy)
          · exact ha'
      exact hdisj b hb a hmemA heq.symm
    have hm := consLookup_foldl_nodup left (buildConsMapSeq right) hnLeft hshardDisj k
    cases hlook : consLookup (buildConsMapSeq (left ++ right)) k with
    | none =>
      have habs : ∀ v, (k, v) ∉ left ++ right := fun v hv => by
        have hs := (consLookup_build_nodup hnSplit k v).mpr hv
        rw [hlook] at hs; cases hs
      have hleftNone : ∀ v, (k, v) ∉ left := fun v hv => habs v (List.mem_append_left right hv)
      have hrightNone : ∀ v, (k, v) ∉ right := fun v hv => habs v (List.mem_append_right left hv)
      have hmerge : consLookup (mergeConsShards left (buildConsMapSeq right)) k =
          consLookup (buildConsMapSeq right) k := hm.2 hleftNone
      have hrightLookup : consLookup (buildConsMapSeq right) k = none := by
        cases hr : consLookup (buildConsMapSeq right) k with
        | none => rfl
        | some v => exact absurd ((consLookup_build_nodup hnRight k v).mp hr) (hrightNone v)
      rw [hmerge, hrightLookup]
    | some v =>
      have hmem : (k, v) ∈ left ++ right := (consLookup_build_nodup hnSplit k v).mp hlook
      rcases List.mem_append.mp hmem with hL | hR
      · exact hm.1 v hL
      · have hleftAbs : ∀ w, (k, w) ∉ left := fun w hw =>
          hdisj (k, w) hw (k, v) hR rfl
        unfold mergeConsShards
        rw [hm.2 hleftAbs]
        exact (consLookup_build_nodup hnRight k v).mpr hR


/-! ### 4. WGSL `exec_whnf_core` Phase-3 `ETAG_APP` Spine Re-Peel & `Quot.lift` Reduction -/

/-- Minimal expression AST capturing applicative spines (`ETAG_APP`), lambdas (`ETAG_LAM`),
    projections (`Proj`), and kernel constants (`Quot.lift`, `Quot.mk`, etc.) modeled in
    `typecheck_whnf.wgsl` `exec_whnf_core`. -/
inductive SpineExpr where
  | atom (tag : Nat)
  | const (cid : Nat)
  | lam (body : SpineExpr)
  | proj (idx : Nat) (inner : SpineExpr)
  | app (fn arg : SpineExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Distinguishes non-stuck application spines (`word_tag == ETAG_APP`). -/
def SpineExpr.isApp : SpineExpr -> Bool
  | .app _ _ => true
  | _ => false

/-- Rebuilds `(((hd arg_0) arg_1) ... arg_{n-1})`, modeling `mk_app_slice(p_res0, buf_ptr, 0, argc)`. -/
def mkAppSlice (hd : SpineExpr) : List SpineExpr -> SpineExpr
  | [] => hd
  | a :: rest => mkAppSlice (.app hd a) rest

private def peelSpineAux : SpineExpr -> List SpineExpr -> SpineExpr × List SpineExpr
  | .app f a, acc => peelSpineAux f (a :: acc)
  | hd, acc => (hd, acc)

/-- Peels a nested application tree into `(head, args)` in application order (`phase == 0u`). -/
def peelSpine (e : SpineExpr) : SpineExpr × List SpineExpr :=
  peelSpineAux e []

/-- Kernel constant IDs for quotient primitives (`Quot.lift`, `Quot.mk`). -/
def quotLiftCid : Nat := 1
def quotMkCid : Nat := 2

/-- Beta-like application substitution parameterised over a body reducer (abstracting `OP_INST_REV`). -/
inductive SpineStep (redAtom : Nat -> Option SpineExpr) (redProj : Nat -> SpineExpr -> Option SpineExpr) :
    SpineExpr -> SpineExpr -> Prop where
  | refl (e : SpineExpr) : SpineStep redAtom redProj e e
  | step_trans {a b c : SpineExpr} :
      SpineStep redAtom redProj a b ->
      SpineStep redAtom redProj b c ->
      SpineStep redAtom redProj a c
  | app_fn {f f' a : SpineExpr} :
      SpineStep redAtom redProj f f' ->
      SpineStep redAtom redProj (.app f a) (.app f' a)
  | app_arg {f a a' : SpineExpr} :
      SpineStep redAtom redProj a a' ->
      SpineStep redAtom redProj (.app f a) (.app f a')
  | atom_delta {t : Nat} {e' : SpineExpr} :
      redAtom t = some e' ->
      SpineStep redAtom redProj (.atom t) e'
  | proj_iota {idx : Nat} {inner e' : SpineExpr} :
      redProj idx inner = some e' ->
      SpineStep redAtom redProj (.proj idx inner) e'
  | quot_lift_iota (α r β f h qα qx : SpineExpr) :
      SpineStep redAtom redProj
        (mkAppSlice (.const quotLiftCid) [α, r, β, f, h, mkAppSlice (.const quotMkCid) [qα, qx]])
        (.app f qx)

private theorem mkAppSlice_append (hd : SpineExpr) (xs ys : List SpineExpr) :
    mkAppSlice (mkAppSlice hd xs) ys = mkAppSlice hd (xs ++ ys) := by
  induction xs generalizing hd with
  | nil => rfl
  | cons x xs ih =>
    change mkAppSlice (mkAppSlice (.app hd x) xs) ys = mkAppSlice (.app hd x) (xs ++ ys)
    exact ih (.app hd x)

private theorem peelSpineAux_mkAppSlice_gen (hd : SpineExpr) (xs acc : List SpineExpr) :
    peelSpineAux (mkAppSlice hd xs) acc = peelSpineAux hd (xs ++ acc) := by
  induction xs generalizing hd acc with
  | nil => rfl
  | cons x xs ih =>
    unfold mkAppSlice
    rw [ih (.app hd x) acc]
    rfl

private theorem peelSpine_mkAppSlice (hd : SpineExpr) (hnot : hd.isApp = false)
    (xs : List SpineExpr) :
    peelSpine (mkAppSlice hd xs) = (hd, xs) := by
  unfold peelSpine
  rw [peelSpineAux_mkAppSlice_gen]
  cases hd with
  | atom _ | const _ | lam _ | proj _ _ => simp [peelSpineAux]
  | app _ _ => cases hnot

private theorem peelSpineAux_sound (e : SpineExpr) (acc : List SpineExpr) :
    let res := peelSpineAux e acc
    mkAppSlice res.1 res.2 = mkAppSlice e acc := by
  induction e generalizing acc with
  | atom _ | const _ | lam _ | proj _ _ => rfl
  | app f a ihf _ =>
    unfold peelSpineAux
    simpa [mkAppSlice] using ihf (a :: acc)

private theorem peelSpine_sound (e : SpineExpr) :
    let res := peelSpine e
    mkAppSlice res.1 res.2 = e :=
  peelSpineAux_sound e []

private theorem spineStep_mkAppSlice {redAtom redProj} {f f' : SpineExpr}
    (hf : SpineStep redAtom redProj f f') (args : List SpineExpr) :
    SpineStep redAtom redProj (mkAppSlice f args) (mkAppSlice f' args) := by
  induction args generalizing f f' with
  | nil => exact hf
  | cons a rest ih => exact ih (SpineStep.app_fn hf)

private theorem spineStep_quotLift_maj {redAtom redProj}
    (α r β f h maj maj' : SpineExpr) (hmaj : SpineStep redAtom redProj maj maj') :
    SpineStep redAtom redProj
      (mkAppSlice (.const quotLiftCid) [α, r, β, f, h, maj])
      (mkAppSlice (.const quotLiftCid) [α, r, β, f, h, maj']) :=
  SpineStep.app_arg hmaj

/-- Phase-4 head dispatch after `(hd2, args)` is in hand (`Quot.lift` iota when
    `hd2 = .const quotLiftCid` and 6+ args are present, using `normMaj` on the major premise). -/
def whnfPhase4Dispatch (normMaj : SpineExpr -> SpineExpr) (cont : SpineExpr -> SpineExpr)
    (hd2 : SpineExpr) (args : List SpineExpr) : SpineExpr :=
  if hd2 == .const quotLiftCid then
    match args with
    | α :: r :: β :: f :: h :: maj :: extra =>
      let maj' := normMaj maj
      match peelSpine maj' with
      | (.const cid, [_, qx]) =>
        if cid == quotMkCid then cont (mkAppSlice (.app f qx) extra)
        else mkAppSlice hd2 (α :: r :: β :: f :: h :: maj' :: extra)
      | _ => mkAppSlice hd2 (α :: r :: β :: f :: h :: maj' :: extra)
    | _ => mkAppSlice hd2 args
  else
    mkAppSlice hd2 args

/-- Phase-3 WGSL `exec_whnf_core` WHNF reducer (`typecheck_whnf.wgsl` lines 828-843):
    1. Peel `(hd, args) := peelSpine e` (`phase = 0`).
    2. Reduce head `hd -> hd2` (`atom` / `proj` / direct `Quot.lift` spine).
    3. If `hd2.isApp` (`word_tag == ETAG_APP`), rebuild `mkAppSlice hd2 args` and restart
       `phase = 0` (`whnfPhase3Fuel ... fuel (mkAppSlice hd2 args)`) so the full combined
       spine is re-peeled instead of falling through to `phase = 4` unreduced. -/
def whnfPhase3Fuel (redAtom : Nat -> Option SpineExpr)
    (redProj : Nat -> SpineExpr -> Option SpineExpr) : Nat -> SpineExpr -> SpineExpr
  | 0, e => e
  | fuel + 1, e =>
    let sp := peelSpine e
    let normMaj := whnfPhase3Fuel redAtom redProj fuel
    let cont := whnfPhase3Fuel redAtom redProj fuel
    match sp.1 with
    | .atom t =>
      match redAtom t with
      | some hd2 =>
        if hd2.isApp then
          whnfPhase3Fuel redAtom redProj fuel (mkAppSlice hd2 sp.2)
        else
          whnfPhase4Dispatch normMaj cont hd2 sp.2
      | none => e
    | .proj idx inner =>
      match redProj idx inner with
      | some hd2 =>
        if hd2.isApp then
          whnfPhase3Fuel redAtom redProj fuel (mkAppSlice hd2 sp.2)
        else
          whnfPhase4Dispatch normMaj cont hd2 sp.2
      | none => e
    | .const cid =>
      if cid == quotLiftCid then
        whnfPhase4Dispatch normMaj cont (.const cid) sp.2
      else
        e
    | .lam _ | .app _ _ => e

/-- Broken pre-fix Phase-4 dispatch that omits the `phase == 3u` `ETAG_APP` re-peel check:
    when `hd2` is `.app`, `hd2 == .const quotLiftCid` fails and returns `mkAppSlice hd2 args`
    unreduced even when a `Quot.lift` iota redex sits in the combined spine. -/
def whnfPhase4NoRepeel (redProj : Nat -> SpineExpr -> Option SpineExpr)
    (normMaj cont : SpineExpr -> SpineExpr) (e : SpineExpr) : SpineExpr :=
  let sp := peelSpine e
  match sp.1 with
  | .proj idx inner =>
    match redProj idx inner with
    | some hd2 => whnfPhase4Dispatch normMaj cont hd2 sp.2
    | none => e
  | _ => e

private theorem whnfPhase4Dispatch_sound {redAtom redProj}
    {normMaj cont : SpineExpr -> SpineExpr}
    (hMaj : ∀ x, SpineStep redAtom redProj x (normMaj x))
    (hCont : ∀ x, SpineStep redAtom redProj x (cont x))
    (hd2 : SpineExpr) (args : List SpineExpr) :
    SpineStep redAtom redProj (mkAppSlice hd2 args)
      (whnfPhase4Dispatch normMaj cont hd2 args) := by
  unfold whnfPhase4Dispatch
  by_cases hcid : (hd2 == .const quotLiftCid) = true
  · simp only [hcid, ↓reduceIte]
    have hhd : hd2 = .const quotLiftCid := beq_iff_eq.mp hcid
    subst hhd
    cases args with
    | nil => exact SpineStep.refl _
    | cons α args1 =>
      cases args1 with
      | nil => exact SpineStep.refl _
      | cons r args2 =>
        cases args2 with
        | nil => exact SpineStep.refl _
        | cons β args3 =>
          cases args3 with
          | nil => exact SpineStep.refl _
          | cons f args4 =>
            cases args4 with
            | nil => exact SpineStep.refl _
            | cons h args5 =>
              cases args5 with
              | nil => exact SpineStep.refl _
              | cons maj extra =>
                dsimp only
                have hmajStep : SpineStep redAtom redProj
                    (mkAppSlice (.const quotLiftCid) (α :: r :: β :: f :: h :: maj :: extra))
                    (mkAppSlice (.const quotLiftCid) (α :: r :: β :: f :: h :: normMaj maj :: extra)) := by
                  have hpre : mkAppSlice (.const quotLiftCid) (α :: r :: β :: f :: h :: maj :: extra) =
                      mkAppSlice (mkAppSlice (.const quotLiftCid) [α, r, β, f, h, maj]) extra := by
                    rw [mkAppSlice_append]; rfl
                  have hpost : mkAppSlice (.const quotLiftCid) (α :: r :: β :: f :: h :: normMaj maj :: extra) =
                      mkAppSlice (mkAppSlice (.const quotLiftCid) [α, r, β, f, h, normMaj maj]) extra := by
                    rw [mkAppSlice_append]; rfl
                  rw [hpre, hpost]
                  exact spineStep_mkAppSlice (spineStep_quotLift_maj α r β f h maj (normMaj maj) (hMaj maj)) extra
                have hpeel := peelSpine_sound (normMaj maj)
                cases hp : peelSpine (normMaj maj) with
                | mk cid' margs =>
                  cases cid' with
                  | atom _ | lam _ | proj _ _ | app _ _ => exact hmajStep
                  | const cidv =>
                    cases margs with
                    | nil => exact hmajStep
                    | cons qα rest =>
                      cases rest with
                      | nil => exact hmajStep
                      | cons qx rest2 =>
                        cases rest2 with
                        | cons _ _ => exact hmajStep
                        | nil =>
                          dsimp only
                          by_cases hmk : (cidv == quotMkCid) = true
                          · simp only [hmk, ↓reduceIte]
                            have hmkEq : cidv = quotMkCid := beq_iff_eq.mp hmk
                            rw [hp] at hpeel
                            dsimp only at hpeel
                            rw [← hpeel, hmkEq] at hmajStep
                            have hiota : SpineStep redAtom redProj
                                (mkAppSlice (.const quotLiftCid)
                                  (α :: r :: β :: f :: h :: mkAppSlice (.const quotMkCid) [qα, qx] :: extra))
                                (mkAppSlice (.app f qx) extra) := by
                              have hL : mkAppSlice (.const quotLiftCid)
                                  (α :: r :: β :: f :: h :: mkAppSlice (.const quotMkCid) [qα, qx] :: extra) =
                                  mkAppSlice (mkAppSlice (.const quotLiftCid)
                                    [α, r, β, f, h, mkAppSlice (.const quotMkCid) [qα, qx]]) extra := by
                                rw [mkAppSlice_append]; rfl
                              rw [hL]
                              exact spineStep_mkAppSlice (SpineStep.quot_lift_iota α r β f h qα qx) extra
                            exact SpineStep.step_trans hmajStep
                              (SpineStep.step_trans hiota (hCont (mkAppSlice (.app f qx) extra)))
                          · simp only [hmk, Bool.false_eq_true, ↓reduceIte]
                            exact hmajStep
  · simp only [hcid, Bool.false_eq_true, ↓reduceIte]
    exact SpineStep.refl _

/-- **Theorem (`whnfPhase3AppSpineRepeel_sound`)**:
    Formal soundness of the Phase-3 `ETAG_APP` spine re-peel fix in `typecheck_whnf.wgsl`
    (`phase == 3u`, lines 828-843):
    1. Rebuilding `mkAppSlice (mkAppSlice base hdArgs) outerArgs` equals
       `mkAppSlice base (hdArgs ++ outerArgs)`, and when `base.isApp = false`, jumping back
       to `phase = 0` (`peelSpine`) peels the exact flattened combined spine
       `(base, hdArgs ++ outerArgs)`.
    2. For any atom/projection rules `redAtom`, `redProj`, fuel `n`, and input `e`,
       `whnfPhase3Fuel` preserves kernel `SpineStep` soundness (`SpineStep redAtom redProj e (whnfPhase3Fuel ... n e)`). -/
theorem whnfPhase3AppSpineRepeel_sound
    (redAtom : Nat -> Option SpineExpr)
    (redProj : Nat -> SpineExpr -> Option SpineExpr) :
    (∀ (base : SpineExpr) (hdArgs outerArgs : List SpineExpr),
      mkAppSlice (mkAppSlice base hdArgs) outerArgs = mkAppSlice base (hdArgs ++ outerArgs) ∧
      (base.isApp = false ->
        peelSpine (mkAppSlice (mkAppSlice base hdArgs) outerArgs) = (base, hdArgs ++ outerArgs))) ∧
    (∀ (fuel : Nat) (e : SpineExpr),
      SpineStep redAtom redProj e (whnfPhase3Fuel redAtom redProj fuel e)) := by
  refine ⟨?_, ?_⟩
  · intro base hdArgs outerArgs
    refine ⟨mkAppSlice_append base hdArgs outerArgs, fun hnot => ?_⟩
    rw [mkAppSlice_append]
    exact peelSpine_mkAppSlice base hnot (hdArgs ++ outerArgs)
  · intro fuel
    induction fuel with
    | zero => intro e; exact SpineStep.refl e
    | succ fuel ih =>
      intro e
      rw [whnfPhase3Fuel.eq_2]
      have hpeel : mkAppSlice (peelSpine e).1 (peelSpine e).2 = e := peelSpine_sound e
      cases hsp : (peelSpine e).1 with
      | atom t =>
        dsimp only
        cases hred : redAtom t with
        | none => exact SpineStep.refl e
        | some hd2 =>
          dsimp only
          have hstep1 : SpineStep redAtom redProj e (mkAppSlice hd2 (peelSpine e).2) := by
            have h0 : SpineStep redAtom redProj (mkAppSlice (.atom t) (peelSpine e).2)
                (mkAppSlice hd2 (peelSpine e).2) :=
              spineStep_mkAppSlice (SpineStep.atom_delta hred) (peelSpine e).2
            rw [← hsp, hpeel] at h0
            exact h0
          by_cases happ : hd2.isApp = true
          · simp only [happ, ↓reduceIte]
            exact SpineStep.step_trans hstep1 (ih (mkAppSlice hd2 (peelSpine e).2))
          · have happf : hd2.isApp = false := Bool.eq_false_iff.mpr happ
            simp only [happf, Bool.false_eq_true, ↓reduceIte]
            exact SpineStep.step_trans hstep1 (whnfPhase4Dispatch_sound ih ih hd2 (peelSpine e).2)
      | proj idx inner =>
        dsimp only
        cases hred : redProj idx inner with
        | none => exact SpineStep.refl e
        | some hd2 =>
          dsimp only
          have hstep1 : SpineStep redAtom redProj e (mkAppSlice hd2 (peelSpine e).2) := by
            have h0 : SpineStep redAtom redProj (mkAppSlice (.proj idx inner) (peelSpine e).2)
                (mkAppSlice hd2 (peelSpine e).2) :=
              spineStep_mkAppSlice (SpineStep.proj_iota hred) (peelSpine e).2
            rw [← hsp, hpeel] at h0
            exact h0
          by_cases happ : hd2.isApp = true
          · simp only [happ, ↓reduceIte]
            exact SpineStep.step_trans hstep1 (ih (mkAppSlice hd2 (peelSpine e).2))
          · have happf : hd2.isApp = false := Bool.eq_false_iff.mpr happ
            simp only [happf, Bool.false_eq_true, ↓reduceIte]
            exact SpineStep.step_trans hstep1 (whnfPhase4Dispatch_sound ih ih hd2 (peelSpine e).2)
      | const cid =>
        dsimp only
        by_cases hcid : (cid == quotLiftCid) = true
        · simp only [hcid, ↓reduceIte]
          have hdis := whnfPhase4Dispatch_sound ih ih (.const cid) (peelSpine e).2
          have hpeel' : mkAppSlice (.const cid) (peelSpine e).2 = e := by
            rw [← hsp]; exact hpeel
          rw [hpeel'] at hdis
          exact hdis
        · simp only [hcid, Bool.false_eq_true, ↓reduceIte]
          exact SpineStep.refl e
      | lam _ => exact SpineStep.refl e
      | app _ _ => exact SpineStep.refl e

/-- **Theorem (`quotLiftSpineReduce_sound`)**:
    When reducing a projection/head `projExpr = .proj idx inner` yields an under-applied
    `Quot.lift` application `hd2 = mkAppSlice (.const quotLiftCid) [α, r, β, f, h]`
    (`hd2.isApp = true`), applied to `maj :: extra` where `maj` normalizes to
    `Quot.mk qα qx`:
    1. Pre-fix `whnfPhase4NoRepeel` fails to detect `quotLiftCid` (`hd2 ≠ .const quotLiftCid`)
       and leaves the entire `App` spine `mkAppSlice hd2 (maj :: extra)` unreduced.
    2. Post-fix `whnfPhase3Fuel` (`fuel ≥ 2`) re-peels `(.const quotLiftCid, [α, r, β, f, h, maj] ++ extra)`,
       triggers `Quot.lift` iota to `whnfPhase3Fuel ... fuel (mkAppSlice (.app f qx) extra)`,
       and is kernel-sound (`SpineStep redAtom redProj (mkAppSlice (.proj idx inner) (maj :: extra)) result`). -/
theorem quotLiftSpineReduce_sound
    (redAtom : Nat -> Option SpineExpr)
    (redProj : Nat -> SpineExpr -> Option SpineExpr)
    (idx : Nat) (inner α r β f h maj qα qx : SpineExpr) (extra : List SpineExpr) (fuel : Nat)
    (hred : redProj idx inner = some (mkAppSlice (.const quotLiftCid) [α, r, β, f, h]))
    (hmaj : whnfPhase3Fuel redAtom redProj fuel maj = mkAppSlice (.const quotMkCid) [qα, qx]) :
    let hd2 := mkAppSlice (.const quotLiftCid) [α, r, β, f, h]
    let fullExpr := mkAppSlice (.proj idx inner) (maj :: extra)
    hd2.isApp = true ∧
    whnfPhase4NoRepeel redProj (whnfPhase3Fuel redAtom redProj fuel)
        (whnfPhase3Fuel redAtom redProj fuel) fullExpr =
      mkAppSlice hd2 (maj :: extra) ∧
    whnfPhase3Fuel redAtom redProj (fuel + 2) fullExpr =
      whnfPhase3Fuel redAtom redProj fuel (mkAppSlice (.app f qx) extra) ∧
    SpineStep redAtom redProj fullExpr
      (whnfPhase3Fuel redAtom redProj (fuel + 2) fullExpr) := by
  have hd2_app : (mkAppSlice (.const quotLiftCid) [α, r, β, f, h]).isApp = true := rfl
  have hd2_ne : (mkAppSlice (.const quotLiftCid) [α, r, β, f, h] == .const quotLiftCid) = false := rfl
  have hpeelFull : peelSpine (mkAppSlice (.proj idx inner) (maj :: extra)) =
      (.proj idx inner, maj :: extra) :=
    peelSpine_mkAppSlice (.proj idx inner) rfl (maj :: extra)
  have hpeelCombined : peelSpine (mkAppSlice (mkAppSlice (.const quotLiftCid) [α, r, β, f, h]) (maj :: extra)) =
      (.const quotLiftCid, α :: r :: β :: f :: h :: maj :: extra) := by
    rw [mkAppSlice_append]
    exact peelSpine_mkAppSlice (.const quotLiftCid) rfl (α :: r :: β :: f :: h :: maj :: extra)
  have hpeelMk : peelSpine (mkAppSlice (.const quotMkCid) [qα, qx]) =
      (.const quotMkCid, [qα, qx]) :=
    peelSpine_mkAppSlice (.const quotMkCid) rfl [qα, qx]
  refine ⟨hd2_app, ?_, ?_, ?_⟩
  · unfold whnfPhase4NoRepeel
    rw [hpeelFull]
    dsimp only
    rw [hred]
    dsimp only
    unfold whnfPhase4Dispatch
    simp [hd2_ne]
  · have hstep1 : whnfPhase3Fuel redAtom redProj (fuel + 2)
        (mkAppSlice (.proj idx inner) (maj :: extra)) =
        whnfPhase3Fuel redAtom redProj (fuel + 1)
          (mkAppSlice (mkAppSlice (.const quotLiftCid) [α, r, β, f, h]) (maj :: extra)) := by
      rw [whnfPhase3Fuel.eq_2]
      rw [hpeelFull]
      dsimp only
      rw [hred]
      dsimp only
      simp [hd2_app]
    have hstep2 : whnfPhase3Fuel redAtom redProj (fuel + 1)
        (mkAppSlice (mkAppSlice (.const quotLiftCid) [α, r, β, f, h]) (maj :: extra)) =
        whnfPhase3Fuel redAtom redProj fuel (mkAppSlice (.app f qx) extra) := by
      rw [whnfPhase3Fuel.eq_2]
      rw [hpeelCombined]
      dsimp only
      unfold whnfPhase4Dispatch
      simp [hmaj, hpeelMk]
    exact hstep1.trans hstep2
  · exact (whnfPhase3AppSpineRepeel_sound redAtom redProj).2 (fuel + 2) _

end ConGpuProof
