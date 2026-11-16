/-
ConGpuProof.Phase3Soundness
===========================
Formal Lean 4 verification for con-gpu Phase 3 extensions:
  1. Exact 64-bit two-limb bitwise operations (`nat64Land`, `nat64Lor`, `nat64Xor`).
  2. Checked 64-bit arithmetic (`nat64AddChecked`, `nat64MulChecked`, `nat64PowChecked`)
     and fuel-bounded Euclidean GCD (`nat64Gcd`).
  3. Speculative same-head spine congruence (`sameHeadSpine_defeq_sound`) across
     `Opaque` / `Abbrev` / `Regular` reducibility hints with safe fallback.
  4. Zero-field single-constructor non-`Prop` structure eta congruence
     (`zeroFieldEta_defeq_sound`, modeling `Unit` / `PUnit` eta).
  5. Epoch-tagged `(a, b, depth, job_epoch)` `DEFEQ` memo soundness caching only
     conclusive verdicts (`defeqEpochMemo_hit_sound`, `advanceEpoch_preserves_defeqMemo`).
  6. Two-ended GPU/CPU hybrid work-stealing over `[0..N)` (`twoEndedHybridSteal_sound`)
     and `CGSNAP02` dual `(GpuArenaPacket, HostEnvSnapshot)` snapshot restoration
     (`dualArenaSnapshot_sound`), preserving exact minimum failure indices.
-/

import ConGpuProof.ArenaOps
import ConGpuProof.StepMachine
import ConGpuProof.Reductions

namespace ConGpuProof

/-! ### 1. Exact 64-bit Limb-Pair Bitwise Operations (`land`, `lor`, `xor`) -/

/-- Exact 64-bit bitwise AND on `(lo, hi)` `UInt32` limb pairs. -/
def nat64Land (a b : Nat64) : Nat64 :=
  (a.1 &&& b.1, a.2 &&& b.2)

/-- Exact 64-bit bitwise OR on `(lo, hi)` `UInt32` limb pairs. -/
def nat64Lor (a b : Nat64) : Nat64 :=
  (a.1 ||| b.1, a.2 ||| b.2)

/-- Exact 64-bit bitwise XOR on `(lo, hi)` `UInt32` limb pairs. -/
def nat64Xor (a b : Nat64) : Nat64 :=
  (a.1 ^^^ b.1, a.2 ^^^ b.2)

private theorem testBit_eq_div_mod2 (n j : Nat) :
    n.testBit j = ((n / 2 ^ j) % 2 == 1) := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]

private theorem nat64_toNat_testBit (x : Nat64) (i : Nat) :
    x.toNat.testBit i = if i < 32 then x.1.toNat.testBit i else x.2.toNat.testBit (i - 32) := by
  unfold Nat64.toNat
  simp only [testBit_eq_div_mod2]
  have hx1 : x.1.toNat < 2 ^ 32 := x.1.toNat_lt_size
  by_cases hi : i < 32
  · simp only [hi, ↓reduceIte]
    have hpowi : 0 < 2 ^ i := Nat.pow_pos (by decide)
    have hpow32 : 2 ^ 32 = 2 ^ (32 - i) * 2 ^ i := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hi)]
    have h2sub : 2 ^ (32 - i) = 2 ^ (32 - i - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    have hdiv : (x.1.toNat + x.2.toNat * 2 ^ 32) / 2 ^ i =
        x.1.toNat / 2 ^ i + x.2.toNat * 2 ^ (32 - i) := by
      rw [hpow32, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ hpowi]
    rw [hdiv, h2sub, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  · simp only [hi, ↓reduceIte]
    have h32 : 32 ≤ i := Nat.le_of_not_lt hi
    have hpow32 : 0 < 2 ^ 32 := Nat.pow_pos (by decide)
    have hpowi : 2 ^ i = 2 ^ 32 * 2 ^ (i - 32) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le h32]
    have hdiv : (x.1.toNat + x.2.toNat * 2 ^ 32) / 2 ^ i =
        x.2.toNat / 2 ^ (i - 32) := by
      rw [hpowi, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ hpow32,
        Nat.div_eq_of_lt hx1, Nat.zero_add]
    rw [hdiv]

/-- **Theorem (`nat64Land_correct`)**:
    Limb-pair bitwise AND agrees identically with `Nat.land`. -/
theorem nat64Land_correct (a b : Nat64) :
    (nat64Land a b).toNat = Nat.land a.toNat b.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (nat64Land a b).toNat.testBit i = (a.toNat &&& b.toNat).testBit i
  rw [Nat.testBit_and, nat64_toNat_testBit, nat64_toNat_testBit, nat64_toNat_testBit]
  unfold nat64Land
  dsimp only
  rw [UInt32.toNat_and, UInt32.toNat_and]
  by_cases hi : i < 32
  · simp only [hi, ↓reduceIte, Nat.testBit_and]
  · simp only [hi, ↓reduceIte, Nat.testBit_and]

/-- **Theorem (`nat64Lor_correct`)**:
    Limb-pair bitwise OR agrees identically with `Nat.lor`. -/
theorem nat64Lor_correct (a b : Nat64) :
    (nat64Lor a b).toNat = Nat.lor a.toNat b.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (nat64Lor a b).toNat.testBit i = (a.toNat ||| b.toNat).testBit i
  rw [Nat.testBit_or, nat64_toNat_testBit, nat64_toNat_testBit, nat64_toNat_testBit]
  unfold nat64Lor
  dsimp only
  rw [UInt32.toNat_or, UInt32.toNat_or]
  by_cases hi : i < 32
  · simp only [hi, ↓reduceIte, Nat.testBit_or]
  · simp only [hi, ↓reduceIte, Nat.testBit_or]

/-- **Theorem (`nat64Xor_correct`)**:
    Limb-pair bitwise XOR agrees identically with `Nat.xor`. -/
theorem nat64Xor_correct (a b : Nat64) :
    (nat64Xor a b).toNat = Nat.xor a.toNat b.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (nat64Xor a b).toNat.testBit i = (a.toNat ^^^ b.toNat).testBit i
  rw [Nat.testBit_xor, nat64_toNat_testBit, nat64_toNat_testBit, nat64_toNat_testBit]
  unfold nat64Xor
  dsimp only
  rw [UInt32.toNat_xor, UInt32.toNat_xor]
  by_cases hi : i < 32
  · simp only [hi, ↓reduceIte, Nat.testBit_xor]
  · simp only [hi, ↓reduceIte, Nat.testBit_xor]

/-! ### 2. Checked 64-bit Arithmetic (`Add`, `Mul`, `Pow`) & Bounded `Gcd` -/

private theorem ui32_add_toNat_cases (x y : UInt32) :
    (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := by
  rw [UInt32.toNat_add]

private theorem ui32_add_carry_iff (x y : UInt32) :
    ((x + y < x) ↔ 2 ^ 32 ≤ x.toNat + y.toNat) ∧
    ((if x + y < x then 2 ^ 32 else 0) + (x + y).toNat = x.toNat + y.toNat) := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
  have hy : y.toNat < 2 ^ 32 := y.toNat_lt_size
  have hadd : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := ui32_add_toNat_cases x y
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

private def mkAddRes (lo hi : UInt32) (ov : Bool) : Option Nat64 :=
  if ov then none else some (lo, hi)

/-- Checked 64-bit limb-pair addition; returns `none` iff `a.toNat + b.toNat ≥ 2^64`. -/
def nat64AddChecked (a b : Nat64) : Option Nat64 :=
  let lo := a.1 + b.1
  let carryLo : UInt32 := if lo < a.1 then 1 else 0
  let hiTmp := a.2 + b.2
  let carry1 := decide (hiTmp < a.2)
  let hi := hiTmp + carryLo
  let carry2 := decide (hi < hiTmp)
  mkAddRes lo hi (carry1 || carry2)

private theorem nat64_limbs_lt_2p64 {lo hi : Nat} (h1 : lo < 2 ^ 32) (h2 : hi < 2 ^ 32) :
    lo + hi * 2 ^ 32 < 2 ^ 64 := by
  have h1' : lo ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt h1
  have h2' : hi ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt h2
  have hmul : hi * 2 ^ 32 ≤ (2 ^ 32 - 1) * 2 ^ 32 := Nat.mul_le_mul_right _ h2'
  have hpow : (2 ^ 32 - 1) + (2 ^ 32 - 1) * 2 ^ 32 + 1 = 2 ^ 64 := by decide
  have hsum : lo + hi * 2 ^ 32 ≤ (2 ^ 32 - 1) + (2 ^ 32 - 1) * 2 ^ 32 := Nat.add_le_add h1' hmul
  exact Nat.lt_of_le_of_lt hsum (by rw [← hpow]; exact Nat.lt_succ_self _)

private theorem nat64Add_sum_identity
    (a1 b1 a2 b2 lo hiTmp hi cLo : Nat) (f0 f1 f2 : Bool)
    (hcarry : cLo = if f0 then 1 else 0)
    (hlo : (if f0 then 2 ^ 32 else 0) + lo = a1 + b1)
    (hhitmp : (if f1 then 2 ^ 32 else 0) + hiTmp = a2 + b2)
    (hhi : (if f2 then 2 ^ 32 else 0) + hi = hiTmp + cLo) :
    lo + hi * 2 ^ 32 +
      ((if f1 then 2 ^ 64 else 0) + (if f2 then 2 ^ 64 else 0)) =
    (a1 + a2 * 2 ^ 32) + (b1 + b2 * 2 ^ 32) := by
  have hpow : (2 ^ 32 * 2 ^ 32 : Nat) = 2 ^ 64 := by decide
  have hlo' : lo + cLo * 2 ^ 32 = a1 + b1 := by
    cases f0 <;> simp only [↓reduceIte, Bool.false_eq_true] at hcarry hlo
    · rw [hcarry, Nat.zero_mul, Nat.add_zero]; rw [Nat.zero_add] at hlo; exact hlo
    · rw [hcarry, Nat.one_mul]; rw [Nat.add_comm] at hlo; exact hlo
  have h1 : hiTmp * 2 ^ 32 + (if f1 then 2 ^ 64 else 0) = (a2 + b2) * 2 ^ 32 := by
    cases f1 <;> simp only [↓reduceIte, Bool.false_eq_true] at hhitmp ⊢
    · rw [Nat.zero_add] at hhitmp; rw [Nat.add_zero, hhitmp]
    · rw [← hhitmp, Nat.add_mul, hpow, Nat.add_comm (2 ^ 64)]
  have h2 : hi * 2 ^ 32 + (if f2 then 2 ^ 64 else 0) = hiTmp * 2 ^ 32 + cLo * 2 ^ 32 := by
    cases f2 <;> simp only [↓reduceIte, Bool.false_eq_true] at hhi ⊢
    · rw [Nat.zero_add] at hhi; rw [Nat.add_zero, hhi, Nat.add_mul]
    · rw [← Nat.add_mul, ← hhi, Nat.add_mul, hpow, Nat.add_comm (2 ^ 64)]
  calc lo + hi * 2 ^ 32 + ((if f1 then 2 ^ 64 else 0) + (if f2 then 2 ^ 64 else 0))
      = lo + (hi * 2 ^ 32 + (if f2 then 2 ^ 64 else 0)) + (if f1 then 2 ^ 64 else 0) := by
        rw [Nat.add_comm (if f1 then 2 ^ 64 else 0) (if f2 then 2 ^ 64 else 0),
            ← Nat.add_assoc (lo + hi * 2 ^ 32), Nat.add_assoc lo (hi * 2 ^ 32)]
    _ = lo + (hiTmp * 2 ^ 32 + cLo * 2 ^ 32) + (if f1 then 2 ^ 64 else 0) := by rw [h2]
    _ = (lo + cLo * 2 ^ 32) + (hiTmp * 2 ^ 32 + (if f1 then 2 ^ 64 else 0)) := by
        rw [Nat.add_comm (hiTmp * 2 ^ 32) (cLo * 2 ^ 32), ← Nat.add_assoc lo,
            Nat.add_assoc (lo + cLo * 2 ^ 32)]
    _ = (a1 + b1) + (a2 + b2) * 2 ^ 32 := by rw [hlo', h1]
    _ = (a1 + a2 * 2 ^ 32) + (b1 + b2 * 2 ^ 32) := by
        rw [Nat.add_mul, Nat.add_assoc a1, Nat.add_comm b1,
            Nat.add_assoc (a2 * 2 ^ 32), Nat.add_comm (b2 * 2 ^ 32) b1, ← Nat.add_assoc a1]

private theorem nat64Add_noOv_aux (x M y : Nat) (h_lt : x < M)
    (hsum : x + ((if false then M else 0) + (if false then M else 0)) = y) :
    x = y ∧ ¬ M ≤ y := by
  have hx : x = y := by
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hsum
  refine ⟨hx, ?_⟩
  rw [← hx]
  exact Nat.not_le_of_gt h_lt

private theorem nat64Add_ov_aux (x M y : Nat) (f1 f2 : Bool)
    (hsum : x + ((if f1 then M else 0) + (if f2 then M else 0)) = y)
    (hor : (f1 || f2) = true) :
    M ≤ y := by
  rw [← hsum]
  cases f1 <;> cases f2
  · cases hor
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact Nat.le_add_left M x
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Nat.le_add_left M x
  · simp only [↓reduceIte]
    exact Nat.le_trans (Nat.le_add_left M M) (Nat.le_add_left (M + M) x)

private theorem nat64Add_cases_aux (a1 a2 b1 b2 lo carryLo hiTmp hi : Nat)
    (f0 f1 f2 : Bool)
    (hlo_lt : lo < 2 ^ 32) (hhi_lt : hi < 2 ^ 32)
    (hcarry : carryLo = if f0 then 1 else 0)
    (hlo : (if f0 then 2 ^ 32 else 0) + lo = a1 + b1)
    (hhitmp : (if f1 then 2 ^ 32 else 0) + hiTmp = a2 + b2)
    (hhi : (if f2 then 2 ^ 32 else 0) + hi = hiTmp + carryLo) :
    ((f1 || f2) = false →
      lo + hi * 2 ^ 32 = (a1 + a2 * 2 ^ 32) + (b1 + b2 * 2 ^ 32) ∧
      ¬ 2 ^ 64 ≤ (a1 + a2 * 2 ^ 32) + (b1 + b2 * 2 ^ 32)) ∧
    ((f1 || f2) = true →
      2 ^ 64 ≤ (a1 + a2 * 2 ^ 32) + (b1 + b2 * 2 ^ 32)) := by
  have hsum := nat64Add_sum_identity a1 b1 a2 b2 lo hiTmp hi carryLo f0 f1 f2
    hcarry hlo hhitmp hhi
  have h64_lt : lo + hi * 2 ^ 32 < 2 ^ 64 := nat64_limbs_lt_2p64 hlo_lt hhi_lt
  refine ⟨(fun hor => ?_), (fun hor => ?_)⟩
  · cases f1 <;> cases f2
    · exact nat64Add_noOv_aux (lo + hi * 2 ^ 32) (2 ^ 64)
        ((a1 + a2 * 2 ^ 32) + (b1 + b2 * 2 ^ 32)) h64_lt hsum
    · cases hor
    · cases hor
    · cases hor
  · exact nat64Add_ov_aux (lo + hi * 2 ^ 32) (2 ^ 64)
      ((a1 + a2 * 2 ^ 32) + (b1 + b2 * 2 ^ 32)) f1 f2 hsum hor

/-- **Theorem (`nat64AddChecked_correct`)**:
    `nat64AddChecked` agrees with `Nat.add` on `some r` and delegates (`none`) iff
    the exact sum is at least `2^64`. -/
theorem nat64AddChecked_correct (a b : Nat64) :
    (∀ r, nat64AddChecked a b = some r -> r.toNat = a.toNat + b.toNat) ∧
    (nat64AddChecked a b = none ↔ 2 ^ 64 ≤ a.toNat + b.toNat) := by
  unfold nat64AddChecked mkAddRes Nat64.toNat
  dsimp only
  have hcLo := ui32_add_carry_iff a.1 b.1
  have hc1 := ui32_add_carry_iff a.2 b.2
  have hc2 := ui32_add_carry_iff (a.2 + b.2) (if a.1 + b.1 < a.1 then 1 else 0)
  have hcarryLoNat :
      (if a.1 + b.1 < a.1 then (1 : UInt32) else 0).toNat =
        if decide (a.1 + b.1 < a.1) then 1 else 0 := by
    by_cases h : a.1 + b.1 < a.1
    · simp only [h, ↓reduceIte, decide_eq_true_eq]; rfl
    · simp only [h, ↓reduceIte, decide_eq_true_eq]; rfl
  have haux := nat64Add_cases_aux
    a.1.toNat a.2.toNat b.1.toNat b.2.toNat
    (a.1 + b.1).toNat (if a.1 + b.1 < a.1 then (1 : UInt32) else 0).toNat
    (a.2 + b.2).toNat ((a.2 + b.2) + (if a.1 + b.1 < a.1 then 1 else 0)).toNat
    (decide (a.1 + b.1 < a.1))
    (decide (a.2 + b.2 < a.2))
    (decide ((a.2 + b.2) + (if a.1 + b.1 < a.1 then 1 else 0) < a.2 + b.2))
    (a.1 + b.1).toNat_lt_size
    ((a.2 + b.2) + (if a.1 + b.1 < a.1 then 1 else 0)).toNat_lt_size
    hcarryLoNat
    (by simp only [decide_eq_true_eq]; exact hcLo.2)
    (by simp only [decide_eq_true_eq]; exact hc1.2)
    (by simp only [decide_eq_true_eq]; exact hc2.2)
  cases hov :
      (decide (a.2 + b.2 < a.2) ||
        decide ((a.2 + b.2) + (if a.1 + b.1 < a.1 then 1 else 0) < a.2 + b.2))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hok := haux.1 hov
    refine ⟨(fun r hr => ?_), ⟨(fun h => by cases h), (fun hge => absurd hge hok.2)⟩⟩
    injection hr with hr'
    rw [← hr']
    exact hok.1
  · simp only [↓reduceIte]
    have hge := haux.2 hov
    exact ⟨(fun _ h => by cases h), ⟨(fun _ => hge), (fun _ => trivial)⟩⟩

private def nat64AddOrZero (a b : Nat64) : Nat64 :=
  (nat64AddChecked a b).getD (0, 0)

private theorem nat64AddOrZero_of_lt {a b : Nat64} (hlt : a.toNat + b.toNat < 2 ^ 64) :
    (nat64AddOrZero a b).toNat = a.toNat + b.toNat := by
  unfold nat64AddOrZero
  have hc := nat64AddChecked_correct a b
  cases h : nat64AddChecked a b with
  | none =>
    have hge := hc.2.mp h
    omega
  | some r =>
    exact hc.1 r h

/-- Exact 32×32 → 64-bit multiplication using 16-bit half-limbs (no `UInt64` required). -/
def mulU32 (x y : UInt32) : Nat64 :=
  let x0 := x &&& 0xffff
  let x1 := x >>> 16
  let y0 := y &&& 0xffff
  let y1 := y >>> 16
  let p00 := x0 * y0
  let p01 := x0 * y1
  let p10 := x1 * y0
  let p11 := x1 * y1
  let mid1 : Nat64 := (p01 <<< 16, p01 >>> 16)
  let mid2 : Nat64 := (p10 <<< 16, p10 >>> 16)
  let s1 := nat64AddOrZero (p00, 0) mid1
  let s2 := nat64AddOrZero s1 mid2
  nat64AddOrZero s2 (0, p11)

private theorem ui32_half_decomp (x : UInt32) :
    (x &&& 0xffff).toNat < 2 ^ 16 ∧
    (x >>> 16).toNat < 2 ^ 16 ∧
    x.toNat = (x &&& 0xffff).toNat + (x >>> 16).toNat * 2 ^ 16 := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt_size
  have hand : (x &&& 0xffff).toNat = x.toNat % 2 ^ 16 := by
    rw [UInt32.toNat_and]
    change Nat.land x.toNat (2 ^ 16 - 1) = x.toNat % 2 ^ 16
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 16
  have hshr : (x >>> 16).toNat = x.toNat / 2 ^ 16 := by
    rw [UInt32.toNat_shiftRight]
    have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
    rw [h16, Nat.shiftRight_eq_div_pow]
  have hdiv : x.toNat / 2 ^ 16 < 2 ^ 16 := by omega
  have hmod : x.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have hsum : x.toNat = x.toNat % 2 ^ 16 + (x.toNat / 2 ^ 16) * 2 ^ 16 := by
    have := Nat.div_add_mod x.toNat (2 ^ 16); omega
  exact ⟨hand ▸ hmod, hshr ▸ hdiv, by rw [hand, hshr]; exact hsum⟩

private theorem ui32_mul_exact {u v : UInt32} (hu : u.toNat < 2 ^ 16) (hv : v.toNat < 2 ^ 16) :
    (u * v).toNat = u.toNat * v.toNat := by
  have hlt : u.toNat * v.toNat < 2 ^ 32 := by
    have h1 : u.toNat ≤ 2 ^ 16 - 1 := by omega
    have h2 : v.toNat ≤ 2 ^ 16 - 1 := by omega
    have hmul := Nat.mul_le_mul h1 h2
    omega
  rw [UInt32.toNat_mul]
  exact Nat.mod_eq_of_lt hlt

private theorem ui32_shift16_pair_toNat (p : UInt32) :
    Nat64.toNat (p <<< 16, p >>> 16) = p.toNat * 2 ^ 16 := by
  unfold Nat64.toNat
  dsimp only
  have hshl : (p <<< 16).toNat = (p.toNat * 2 ^ 16) % 2 ^ 32 := by
    rw [UInt32.toNat_shiftLeft]
    have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
    rw [h16, Nat.shiftLeft_eq]
  have hshr : (p >>> 16).toNat = p.toNat / 2 ^ 16 := by
    rw [UInt32.toNat_shiftRight]
    have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
    rw [h16, Nat.shiftRight_eq_div_pow]
  rw [hshl, hshr]
  have hp : p.toNat < 2 ^ 32 := p.toNat_lt_size
  let q := p.toNat / 2 ^ 16
  let r := p.toNat % 2 ^ 16
  have hdecomp : p.toNat = r + q * 2 ^ 16 := by
    dsimp only [q, r]; have := Nat.div_add_mod p.toNat (2 ^ 16); omega
  have hr : r < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have hmod : ((r + q * 2 ^ 16) * 2 ^ 16) % 2 ^ 32 = r * 2 ^ 16 := by
    have hpow : (2 ^ 16 * 2 ^ 16 : Nat) = 2 ^ 32 := by decide
    rw [Nat.add_mul, Nat.mul_assoc, hpow, Nat.mul_comm q (2 ^ 32), Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hpow32 : p.toNat * 2 ^ 16 = (r + q * 2 ^ 16) * 2 ^ 16 := congrArg (· * 2 ^ 16) hdecomp
  have hmod' : (p.toNat * 2 ^ 16) % 2 ^ 32 = r * 2 ^ 16 := by
    rw [hpow32]; exact hmod
  rw [hmod']
  dsimp only [q, r]
  have hpow : (2 ^ 16 * 2 ^ 16 : Nat) = 2 ^ 32 := by decide
  have hmul : p.toNat % 2 ^ 16 * 2 ^ 16 + p.toNat / 2 ^ 16 * 2 ^ 32 =
      (p.toNat % 2 ^ 16 + p.toNat / 2 ^ 16 * 2 ^ 16) * 2 ^ 16 := by
    rw [Nat.add_mul, Nat.mul_assoc, hpow]
  rw [hmul]
  have hdivadd : p.toNat % 2 ^ 16 + p.toNat / 2 ^ 16 * 2 ^ 16 = p.toNat := by
    have hda := Nat.div_add_mod p.toNat (2 ^ 16)
    omega
  rw [hdivadd]

theorem mulU32_correct (x y : UInt32) : (mulU32 x y).toNat = x.toNat * y.toNat := by
  unfold mulU32
  dsimp only
  obtain ⟨hx0, hx1, hx⟩ := ui32_half_decomp x
  obtain ⟨hy0, hy1, hy⟩ := ui32_half_decomp y
  let x0 := x &&& 0xffff
  let x1 := x >>> 16
  let y0 := y &&& 0xffff
  let y1 := y >>> 16
  change Nat64.toNat (nat64AddOrZero (nat64AddOrZero (nat64AddOrZero (x0 * y0, 0)
      ((x0 * y1) <<< 16, (x0 * y1) >>> 16)) ((x1 * y0) <<< 16, (x1 * y0) >>> 16))
      (0, x1 * y1)) = x.toNat * y.toNat
  have hp00 : (x0 * y0).toNat = x0.toNat * y0.toNat := ui32_mul_exact hx0 hy0
  have hp01 : (x0 * y1).toNat = x0.toNat * y1.toNat := ui32_mul_exact hx0 hy1
  have hp10 : (x1 * y0).toNat = x1.toNat * y0.toNat := ui32_mul_exact hx1 hy0
  have hp11 : (x1 * y1).toNat = x1.toNat * y1.toNat := ui32_mul_exact hx1 hy1
  have hm1 : Nat64.toNat ((x0 * y1) <<< 16, (x0 * y1) >>> 16) = x0.toNat * y1.toNat * 2 ^ 16 := by
    rw [ui32_shift16_pair_toNat, hp01]
  have hm2 : Nat64.toNat ((x1 * y0) <<< 16, (x1 * y0) >>> 16) = x1.toNat * y0.toNat * 2 ^ 16 := by
    rw [ui32_shift16_pair_toNat, hp10]
  have h00_toNat : Nat64.toNat (x0 * y0, (0 : UInt32)) = x0.toNat * y0.toNat := by
    simp [Nat64.toNat, hp00]
  have h11_toNat : Nat64.toNat ((0 : UInt32), x1 * y1) = x1.toNat * y1.toNat * 2 ^ 32 := by
    simp [Nat64.toNat, hp11]
  have hx0' : x0.toNat ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hx0
  have hx1' : x1.toNat ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hx1
  have hy0' : y0.toNat ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hy0
  have hy1' : y1.toNat ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hy1
  have b00 : x0.toNat * y0.toNat ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) :=
    Nat.mul_le_mul hx0' hy0'
  have b01 : x0.toNat * y1.toNat ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) :=
    Nat.mul_le_mul hx0' hy1'
  have b10 : x1.toNat * y0.toNat ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) :=
    Nat.mul_le_mul hx1' hy0'
  have b11 : x1.toNat * y1.toNat ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) :=
    Nat.mul_le_mul hx1' hy1'
  have hs1_lt : Nat64.toNat (x0 * y0, (0 : UInt32)) +
      Nat64.toNat ((x0 * y1) <<< 16, (x0 * y1) >>> 16) < 2 ^ 64 := by
    rw [h00_toNat, hm1]; omega
  have hs1 := nat64AddOrZero_of_lt hs1_lt
  change Nat64.toNat (nat64AddOrZero (x0 * y0, 0) ((x0 * y1) <<< 16, (x0 * y1) >>> 16)) = _ at hs1
  rw [h00_toNat, hm1] at hs1
  have hs2_lt : Nat64.toNat (nat64AddOrZero (x0 * y0, 0) ((x0 * y1) <<< 16, (x0 * y1) >>> 16)) +
      Nat64.toNat ((x1 * y0) <<< 16, (x1 * y0) >>> 16) < 2 ^ 64 := by
    rw [hs1, hm2]; omega
  have hs2 := nat64AddOrZero_of_lt hs2_lt
  change Nat64.toNat (nat64AddOrZero (nat64AddOrZero (x0 * y0, 0) ((x0 * y1) <<< 16, (x0 * y1) >>> 16))
      ((x1 * y0) <<< 16, (x1 * y0) >>> 16)) = _ at hs2
  rw [hs1, hm2] at hs2
  have hs3_lt : Nat64.toNat (nat64AddOrZero (nat64AddOrZero (x0 * y0, 0) ((x0 * y1) <<< 16, (x0 * y1) >>> 16))
      ((x1 * y0) <<< 16, (x1 * y0) >>> 16)) + Nat64.toNat ((0 : UInt32), x1 * y1) < 2 ^ 64 := by
    rw [hs2, h11_toNat]; omega
  have hs3 := nat64AddOrZero_of_lt hs3_lt
  rw [hs2, h11_toNat] at hs3
  rw [hs3, hx, hy]
  have hexpand :
      (x0.toNat + x1.toNat * 2 ^ 16) * (y0.toNat + y1.toNat * 2 ^ 16) =
        x0.toNat * y0.toNat + x0.toNat * y1.toNat * 2 ^ 16 +
        x1.toNat * y0.toNat * 2 ^ 16 + x1.toNat * y1.toNat * 2 ^ 32 := by
    have hpow32 : (2 ^ 16 * 2 ^ 16 : Nat) = 2 ^ 32 := by decide
    calc (x0.toNat + x1.toNat * 2 ^ 16) * (y0.toNat + y1.toNat * 2 ^ 16)
        = x0.toNat * y0.toNat + x0.toNat * (y1.toNat * 2 ^ 16) +
          (x1.toNat * 2 ^ 16) * y0.toNat + (x1.toNat * 2 ^ 16) * (y1.toNat * 2 ^ 16) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
      _ = x0.toNat * y0.toNat + x0.toNat * y1.toNat * 2 ^ 16 +
          x1.toNat * y0.toNat * 2 ^ 16 + x1.toNat * y1.toNat * 2 ^ 32 := by
          have t1 : x0.toNat * (y1.toNat * 2 ^ 16) = x0.toNat * y1.toNat * 2 ^ 16 := by
            rw [Nat.mul_assoc]
          have t2 : (x1.toNat * 2 ^ 16) * y0.toNat = x1.toNat * y0.toNat * 2 ^ 16 := by
            rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 16) y0.toNat, ← Nat.mul_assoc]
          have t3 : (x1.toNat * 2 ^ 16) * (y1.toNat * 2 ^ 16) = x1.toNat * y1.toNat * 2 ^ 32 := by
            calc (x1.toNat * 2 ^ 16) * (y1.toNat * 2 ^ 16)
                = x1.toNat * y1.toNat * (2 ^ 16 * 2 ^ 16) := by rw [Nat.mul_mul_mul_comm]
              _ = x1.toNat * y1.toNat * 2 ^ 32 := by rw [hpow32]
          rw [t1, t2, t3]
  exact hexpand.symm

/-- Checked 64-bit limb-pair multiplication; returns `none` iff `a.toNat * b.toNat ≥ 2^64`. -/
def nat64MulChecked (a b : Nat64) : Option Nat64 :=
  if a.2 != 0 && b.2 != 0 then none
  else
    let p00 := mulU32 a.1 b.1
    let p01 := mulU32 a.1 b.2
    let p10 := mulU32 a.2 b.1
    if p01.2 != 0 || p10.2 != 0 then none
    else
      match nat64AddChecked p00 (0, p01.1) with
      | none => none
      | some t => nat64AddChecked t (0, p10.1)

private theorem nat64_mul_expand (a b : Nat64) :
    a.toNat * b.toNat =
      a.1.toNat * b.1.toNat +
      (a.1.toNat * b.2.toNat) * 2 ^ 32 +
      (a.2.toNat * b.1.toNat) * 2 ^ 32 +
      (a.2.toNat * b.2.toNat) * 2 ^ 64 := by
  unfold Nat64.toNat
  have hpow64 : (2 ^ 32 * 2 ^ 32 : Nat) = 2 ^ 64 := by decide
  calc (a.1.toNat + a.2.toNat * 2 ^ 32) * (b.1.toNat + b.2.toNat * 2 ^ 32)
      = a.1.toNat * b.1.toNat + a.1.toNat * (b.2.toNat * 2 ^ 32) +
        (a.2.toNat * 2 ^ 32) * b.1.toNat + (a.2.toNat * 2 ^ 32) * (b.2.toNat * 2 ^ 32) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    _ = a.1.toNat * b.1.toNat + (a.1.toNat * b.2.toNat) * 2 ^ 32 +
        (a.2.toNat * b.1.toNat) * 2 ^ 32 + (a.2.toNat * b.2.toNat) * 2 ^ 64 := by
        have t1 : a.1.toNat * (b.2.toNat * 2 ^ 32) = (a.1.toNat * b.2.toNat) * 2 ^ 32 := by
          rw [Nat.mul_assoc]
        have t2 : (a.2.toNat * 2 ^ 32) * b.1.toNat = (a.2.toNat * b.1.toNat) * 2 ^ 32 := by
          rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 32) b.1.toNat, ← Nat.mul_assoc]
        have t3 : (a.2.toNat * 2 ^ 32) * (b.2.toNat * 2 ^ 32) = (a.2.toNat * b.2.toNat) * 2 ^ 64 := by
          calc (a.2.toNat * 2 ^ 32) * (b.2.toNat * 2 ^ 32)
              = (a.2.toNat * b.2.toNat) * (2 ^ 32 * 2 ^ 32) := by rw [Nat.mul_mul_mul_comm]
            _ = (a.2.toNat * b.2.toNat) * 2 ^ 64 := by rw [hpow64]
        rw [t1, t2, t3]

private theorem ui32_ne_zero_pos {x : UInt32} (h : (x != 0) = true) : 1 ≤ x.toNat := by
  have hne : x ≠ 0 := bne_iff_ne.mp h
  by_cases hz : x.toNat = 0
  · exfalso; apply hne
    have : UInt32.ofNat x.toNat = x := UInt32.ofNat_toNat
    rw [← this, hz]; rfl
  · omega

private theorem ui32_eq_zero_of_not_bne {x : UInt32} (h : (x != 0) = false) : x.toNat = 0 := by
  have heq : x = 0 := by
    cases hb : (x == 0)
    · have : (x != 0) = true := by simp [bne, hb]
      rw [this] at h; cases h
    · exact beq_iff_eq.mp hb
  rw [heq]; rfl

private theorem nat64Mul_zeroHi_correct (a b : Nat64)
    (hcond : (a.2 != 0 && b.2 != 0) = false)
    (hz : a.2.toNat * b.2.toNat = 0) :
    (∀ r, nat64MulChecked a b = some r -> r.toNat = a.toNat * b.toNat) ∧
    (nat64MulChecked a b = none ↔ 2 ^ 64 ≤ a.toNat * b.toNat) := by
  have hexp : a.toNat * b.toNat =
      a.1.toNat * b.1.toNat +
      (a.1.toNat * b.2.toNat) * 2 ^ 32 +
      (a.2.toNat * b.1.toNat) * 2 ^ 32 := by
    rw [nat64_mul_expand, hz, Nat.zero_mul, Nat.add_zero]
  have hp00 : (mulU32 a.1 b.1).toNat = a.1.toNat * b.1.toNat := mulU32_correct a.1 b.1
  have hp01 : (mulU32 a.1 b.2).toNat = a.1.toNat * b.2.toNat := mulU32_correct a.1 b.2
  have hp10 : (mulU32 a.2 b.1).toNat = a.2.toNat * b.1.toNat := mulU32_correct a.2 b.1
  have hmul_eq : nat64MulChecked a b =
      if (mulU32 a.1 b.2).2 != 0 || (mulU32 a.2 b.1).2 != 0 then none
      else match nat64AddChecked (mulU32 a.1 b.1) (0, (mulU32 a.1 b.2).1) with
        | none => none
        | some t => nat64AddChecked t (0, (mulU32 a.2 b.1).1) := by
    unfold nat64MulChecked
    rw [hcond]
    rfl
  rw [hmul_eq]
  have hpow64 : (2 ^ 32 * 2 ^ 32 : Nat) = 2 ^ 64 := by decide
  cases h01 : ((mulU32 a.1 b.2).2 != 0) <;> cases h10 : ((mulU32 a.2 b.1).2 != 0)
  · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have h01z : (mulU32 a.1 b.2).2.toNat = 0 := ui32_eq_zero_of_not_bne h01
    have h10z : (mulU32 a.2 b.1).2.toNat = 0 := ui32_eq_zero_of_not_bne h10
    have hp01_lo : Nat64.toNat ((0 : UInt32), (mulU32 a.1 b.2).1) = a.1.toNat * b.2.toNat * 2 ^ 32 := by
      rw [← hp01]; unfold Nat64.toNat; simp [h01z]
    have hp10_lo : Nat64.toNat ((0 : UInt32), (mulU32 a.2 b.1).1) = a.2.toNat * b.1.toNat * 2 ^ 32 := by
      rw [← hp10]; unfold Nat64.toNat; simp [h10z]
    have ha1 := nat64AddChecked_correct (mulU32 a.1 b.1) (0, (mulU32 a.1 b.2).1)
    cases hstep1 : nat64AddChecked (mulU32 a.1 b.1) (0, (mulU32 a.1 b.2).1) with
    | none =>
      dsimp only
      have hge1 := ha1.2.mp hstep1
      rw [hp00, hp01_lo] at hge1
      have hge : 2 ^ 64 ≤ a.toNat * b.toNat := by
        rw [hexp]; exact Nat.le_trans hge1 (Nat.le_add_right _ _)
      exact ⟨(fun _ h => by cases h), ⟨(fun _ => hge), (fun _ => rfl)⟩⟩
    | some t =>
      dsimp only
      have ht : t.toNat = a.1.toNat * b.1.toNat + a.1.toNat * b.2.toNat * 2 ^ 32 := by
        rw [ha1.1 t hstep1, hp00, hp01_lo]
      have ha2c := nat64AddChecked_correct t (0, (mulU32 a.2 b.1).1)
      cases hstep2 : nat64AddChecked t (0, (mulU32 a.2 b.1).1) with
      | none =>
        have hge2 := ha2c.2.mp hstep2
        rw [ht, hp10_lo] at hge2
        have hge : 2 ^ 64 ≤ a.toNat * b.toNat := by rw [hexp]; exact hge2
        exact ⟨(fun _ h => by cases h), ⟨(fun _ => hge), (fun _ => rfl)⟩⟩
      | some r =>
        have hr : r.toNat = a.toNat * b.toNat := by
          rw [ha2c.1 r hstep2, ht, hp10_lo, hexp]
        have hlt : ¬ 2 ^ 64 ≤ a.toNat * b.toNat := by
          rw [← hr]; exact Nat.not_le_of_gt (nat64_toNat_lt r)
        exact ⟨(fun r' hr' => by simp only [Option.some.injEq] at hr'; rw [← hr', hr]),
               ⟨(fun h => by cases h), (fun h => absurd h hlt)⟩⟩
  · simp only [Bool.false_or, ↓reduceIte]
    have hv : 2 ^ 32 ≤ a.2.toNat * b.1.toNat := by
      have hm := ui32_ne_zero_pos h10
      rw [← hp10]; unfold Nat64.toNat
      have hmul := Nat.mul_le_mul_right (2 ^ 32) hm
      rw [Nat.one_mul] at hmul
      exact Nat.le_trans hmul (Nat.le_add_left _ _)
    have hmul := Nat.mul_le_mul_right (2 ^ 32) hv
    rw [hpow64] at hmul
    have hge : 2 ^ 64 ≤ a.toNat * b.toNat := by
      rw [hexp]; exact Nat.le_trans hmul (Nat.le_add_left _ _)
    exact ⟨(fun _ h => by cases h), ⟨(fun _ => hge), (fun _ => trivial)⟩⟩
  · simp only [Bool.true_or, ↓reduceIte]
    have hv : 2 ^ 32 ≤ a.1.toNat * b.2.toNat := by
      have hm := ui32_ne_zero_pos h01
      rw [← hp01]; unfold Nat64.toNat
      have hmul := Nat.mul_le_mul_right (2 ^ 32) hm
      rw [Nat.one_mul] at hmul
      exact Nat.le_trans hmul (Nat.le_add_left _ _)
    have hmul := Nat.mul_le_mul_right (2 ^ 32) hv
    rw [hpow64] at hmul
    have hge : 2 ^ 64 ≤ a.toNat * b.toNat := by
      rw [hexp]
      exact Nat.le_trans hmul (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
    exact ⟨(fun _ h => by cases h), ⟨(fun _ => hge), (fun _ => trivial)⟩⟩
  · simp only [Bool.true_or, ↓reduceIte]
    have hv : 2 ^ 32 ≤ a.1.toNat * b.2.toNat := by
      have hm := ui32_ne_zero_pos h01
      rw [← hp01]; unfold Nat64.toNat
      have hmul := Nat.mul_le_mul_right (2 ^ 32) hm
      rw [Nat.one_mul] at hmul
      exact Nat.le_trans hmul (Nat.le_add_left _ _)
    have hmul := Nat.mul_le_mul_right (2 ^ 32) hv
    rw [hpow64] at hmul
    have hge : 2 ^ 64 ≤ a.toNat * b.toNat := by
      rw [hexp]
      exact Nat.le_trans hmul (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
    exact ⟨(fun _ h => by cases h), ⟨(fun _ => hge), (fun _ => trivial)⟩⟩

/-- **Theorem (`nat64MulChecked_correct`)**:
    `nat64MulChecked` agrees with `Nat.mul` on `some r` and returns `none` iff
    the exact product is at least `2^64`. -/
theorem nat64MulChecked_correct (a b : Nat64) :
    (∀ r, nat64MulChecked a b = some r -> r.toNat = a.toNat * b.toNat) ∧
    (nat64MulChecked a b = none ↔ 2 ^ 64 ≤ a.toNat * b.toNat) := by
  cases ha2 : (a.2 != 0) <;> cases hb2 : (b.2 != 0)
  · exact nat64Mul_zeroHi_correct a b (by simp [ha2])
      (by rw [ui32_eq_zero_of_not_bne ha2, Nat.zero_mul])
  · exact nat64Mul_zeroHi_correct a b (by simp [ha2])
      (by rw [ui32_eq_zero_of_not_bne ha2, Nat.zero_mul])
  · exact nat64Mul_zeroHi_correct a b (by simp [hb2])
      (by rw [ui32_eq_zero_of_not_bne hb2, Nat.mul_zero])
  · have hmul_eq : nat64MulChecked a b = none := by
      unfold nat64MulChecked; simp [ha2, hb2]
    rw [hmul_eq]
    have ha2p : 1 ≤ a.2.toNat := ui32_ne_zero_pos ha2
    have hb2p : 1 ≤ b.2.toNat := ui32_ne_zero_pos hb2
    have hm1 : 1 ≤ a.2.toNat * b.2.toNat := Nat.mul_pos ha2p hb2p
    have hm2 := Nat.mul_le_mul_right (2 ^ 64) hm1
    rw [Nat.one_mul] at hm2
    have hge : 2 ^ 64 ≤ a.toNat * b.toNat := by
      rw [nat64_mul_expand]; exact Nat.le_trans hm2 (Nat.le_add_left _ _)
    exact ⟨(fun _ h => by cases h), ⟨(fun _ => hge), (fun _ => rfl)⟩⟩

/-- Fuel-bounded checked 64-bit binary exponentiation loop (`none` delegates on overflow). -/
def nat64PowAux : Nat -> Nat64 -> Nat64 -> Nat64 -> Option Nat64
  | 0, acc, _, exp => if nat64IsZero exp then some acc else none
  | fuel + 1, acc, base, exp =>
    if nat64IsZero exp then some acc
    else
      let accNext? :=
        if (exp.1 &&& 1) != 0 then nat64MulChecked acc base else some acc
      match accNext? with
      | none => none
      | some acc' =>
        let exp' := nat64Shr exp (1, 0)
        if nat64IsZero exp' then some acc'
        else
          match nat64MulChecked base base with
          | none => none
          | some base' => nat64PowAux fuel acc' base' exp'

/-- Checked 64-bit binary exponentiation `a ^ b`; returns `none` iff `a.toNat ^ b.toNat ≥ 2^64`. -/
def nat64PowChecked (a b : Nat64) : Option Nat64 :=
  nat64PowAux 64 (1, 0) a b

private theorem nat64_lsb_mod2 (exp : Nat64) :
    (if ((exp.1 &&& 1) != 0) then 1 else 0) = exp.toNat % 2 := by
  have hb := nat64Bit_correct exp (k := 0) (by decide)
  unfold nat64Bit at hb
  simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.pow_zero, Nat.div_one] at hb
  have hz : (UInt32.ofNat 0 : UInt32) = 0 := rfl
  rw [hz, UInt32.shiftRight_zero] at hb
  exact hb

private theorem nat64Shr1_div2 (exp : Nat64) :
    (nat64Shr exp (1, 0)).toNat = exp.toNat / 2 := by
  rw [nat64Shr_correct, Nat.shiftRight_eq_div_pow]
  have h1 : Nat64.toNat ((1 : UInt32), (0 : UInt32)) = 1 := by simp [Nat64.toNat]
  rw [h1, Nat.pow_one]

private theorem nat64PowAux_correct :
    ∀ (fuel : Nat) (acc base exp : Nat64) (target : Nat),
      exp.toNat < 2 ^ fuel ->
      acc.toNat * base.toNat ^ exp.toNat = target ->
      (base.toNat = 0 ∨ 1 ≤ acc.toNat) ->
      (∀ r, nat64PowAux fuel acc base exp = some r -> r.toNat = target) ∧
      (nat64PowAux fuel acc base exp = none -> 2 ^ 64 ≤ target)
  | 0, acc, base, exp, target, hexp, hinv, _ => by
    have hz : exp.toNat = 0 := by simp at hexp; omega
    have hiz : nat64IsZero exp = true := (nat64IsZero_iff exp).mpr hz
    unfold nat64PowAux
    simp only [hiz, ↓reduceIte]
    rw [hz, Nat.pow_zero, Nat.mul_one] at hinv
    exact ⟨fun r hr => by simp only [Option.some.injEq] at hr; rw [← hr, hinv],
           fun hnone => by cases hnone⟩
  | fuel + 1, acc, base, exp, target, hexp, hinv, hnz => by
    unfold nat64PowAux
    by_cases hez : exp.toNat = 0
    · have hiz : nat64IsZero exp = true := (nat64IsZero_iff exp).mpr hez
      simp only [hiz, ↓reduceIte]
      rw [hez, Nat.pow_zero, Nat.mul_one] at hinv
      exact ⟨fun r hr => by simp only [Option.some.injEq] at hr; rw [← hr, hinv],
             fun hnone => by cases hnone⟩
    · have hizf : nat64IsZero exp = false := by
        cases h : nat64IsZero exp
        · rfl
        · exfalso; exact hez ((nat64IsZero_iff exp).mp h)
      simp only [hizf, Bool.false_eq_true, ↓reduceIte]
      have hlsb := nat64_lsb_mod2 exp
      have hshr := nat64Shr1_div2 exp
      have hexp_decomp : exp.toNat = 2 * (exp.toNat / 2) + exp.toNat % 2 := by omega
      have hexp'_lt : (nat64Shr exp (1, 0)).toNat < 2 ^ fuel := by
        rw [hshr]; have : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := Nat.pow_succ _ _; omega
      have hStepPow (accVal : Nat) (hacc : accVal = if ((exp.1 &&& 1) != 0) then acc.toNat * base.toNat else acc.toNat) :
          accVal * (base.toNat * base.toNat) ^ (exp.toNat / 2) = target := by
        rw [← hinv, hacc, ← Nat.pow_two, ← Nat.pow_mul]
        by_cases hodd : (exp.1 &&& 1) != 0
        · simp only [hodd, ↓reduceIte] at hlsb ⊢
          have hmod1 : exp.toNat % 2 = 1 := hlsb.symm
          calc (acc.toNat * base.toNat) * base.toNat ^ (2 * (exp.toNat / 2))
              = acc.toNat * (base.toNat * base.toNat ^ (2 * (exp.toNat / 2))) := by rw [Nat.mul_assoc]
            _ = acc.toNat * base.toNat ^ (2 * (exp.toNat / 2) + 1) := by
                rw [Nat.pow_succ, Nat.mul_comm (base.toNat ^ _)]
            _ = acc.toNat * base.toNat ^ exp.toNat := by rw [← hmod1, ← hexp_decomp]
        · simp only [hodd, Bool.false_eq_true, ↓reduceIte] at hlsb ⊢
          have hmod0 : exp.toNat % 2 = 0 := hlsb.symm
          have heq : 2 * (exp.toNat / 2) = exp.toNat := by omega
          rw [heq]
      have hBasePowZero : base.toNat = 0 -> (base.toNat * base.toNat) ^ (exp.toNat / 2) = 0 ->
          1 ≤ exp.toNat := fun _ _ => Nat.pos_of_ne_zero hez
      -- Split on accNext?
      cases haccNext : (if ((exp.1 &&& 1) != 0) then nat64MulChecked acc base else some acc) with
      | none =>
        dsimp only
        by_cases hodd : (exp.1 &&& 1) != 0
        · simp only [hodd, ↓reduceIte] at haccNext hlsb
          have hge := (nat64MulChecked_correct acc base).2.mp haccNext
          have hmod1 : exp.toNat % 2 = 1 := hlsb.symm
          have hexp_pos : 1 ≤ exp.toNat := by omega
          have hb_pos : 1 ≤ base.toNat := by
            by_cases hbz : base.toNat = 0
            · rw [hbz, Nat.mul_zero] at hge; omega
            · omega
          have hp_pos : 1 ≤ base.toNat ^ (exp.toNat - 1) := Nat.one_le_pow _ _ hb_pos
          have hle : acc.toNat * base.toNat ≤ target := by
            rw [← hinv]
            have hpow : base.toNat ^ exp.toNat = base.toNat * base.toNat ^ (exp.toNat - 1) := by
              calc base.toNat ^ exp.toNat
                  = base.toNat ^ ((exp.toNat - 1) + 1) := by rw [Nat.sub_add_cancel hexp_pos]
                _ = base.toNat ^ (exp.toNat - 1) * base.toNat := Nat.pow_succ _ _
                _ = base.toNat * base.toNat ^ (exp.toNat - 1) := Nat.mul_comm _ _
            rw [hpow, ← Nat.mul_assoc]
            exact Nat.le_mul_of_pos_right _ hp_pos
          exact ⟨(fun _ h => by cases h), (fun _ => Nat.le_trans hge hle)⟩
        · simp [hodd] at haccNext
      | some acc' =>
        dsimp only
        have ⟨haccVal, hacc_nz⟩ :
            acc'.toNat = (if ((exp.1 &&& 1) != 0) then acc.toNat * base.toNat else acc.toNat) ∧
            (base.toNat = 0 ∨ 1 ≤ acc'.toNat) := by
          by_cases hodd : (exp.1 &&& 1) != 0
          · simp only [hodd, ↓reduceIte] at haccNext ⊢
            have hm := (nat64MulChecked_correct acc base).1 acc' haccNext
            refine ⟨hm, ?_⟩
            rcases hnz with hbz | hacc1
            · exact Or.inl hbz
            · by_cases hbz : base.toNat = 0
              · exact Or.inl hbz
              · right; rw [hm]; exact Nat.mul_pos hacc1 (Nat.pos_of_ne_zero hbz)
          · simp only [hodd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at haccNext ⊢
            rw [← haccNext]
            exact ⟨rfl, hnz⟩
        have hStep := hStepPow acc'.toNat haccVal
        by_cases hexp'z : (nat64Shr exp (1, 0)).toNat = 0
        · have hiz' : nat64IsZero (nat64Shr exp (1, 0)) = true := (nat64IsZero_iff _).mpr hexp'z
          simp only [hiz', ↓reduceIte]
          have hdiv0 : exp.toNat / 2 = 0 := by rw [← hshr]; exact hexp'z
          rw [hdiv0, Nat.pow_zero, Nat.mul_one] at hStep
          exact ⟨fun r hr => by simp only [Option.some.injEq] at hr; rw [← hr, hStep],
                 fun hnone => by cases hnone⟩
        · have hiz'f : nat64IsZero (nat64Shr exp (1, 0)) = false := by
            cases h : nat64IsZero (nat64Shr exp (1, 0))
            · rfl
            · exfalso; exact hexp'z ((nat64IsZero_iff _).mp h)
          simp only [hiz'f, Bool.false_eq_true, ↓reduceIte]
          have hdiv_pos : 1 ≤ exp.toNat / 2 := by rw [← hshr]; omega
          cases hbaseSq : nat64MulChecked base base with
          | none =>
            have hge := (nat64MulChecked_correct base base).2.mp hbaseSq
            have hb_nz : base.toNat ≠ 0 := by
              intro hbz; rw [hbz, Nat.mul_zero] at hge; omega
            have hb_pos : 1 ≤ base.toNat := Nat.pos_of_ne_zero hb_nz
            have hacc_pos : 1 ≤ acc'.toNat := by
              rcases hacc_nz with hbz | h1
              · exact absurd hbz hb_nz
              · exact h1
            have hsq_pos : 1 ≤ base.toNat * base.toNat := Nat.mul_pos hb_pos hb_pos
            have hpow_ge : base.toNat * base.toNat ≤ (base.toNat * base.toNat) ^ (exp.toNat / 2) := by
              calc base.toNat * base.toNat
                  = (base.toNat * base.toNat) ^ 1 := (Nat.pow_one _).symm
                _ ≤ (base.toNat * base.toNat) ^ (exp.toNat / 2) :=
                  Nat.pow_le_pow_right hsq_pos hdiv_pos
            have hle : base.toNat * base.toNat ≤ target := by
              rw [← hStep]
              exact Nat.le_trans hpow_ge (Nat.le_mul_of_pos_left _ hacc_pos)
            exact ⟨(fun _ h => by cases h), (fun _ => Nat.le_trans hge hle)⟩
          | some base' =>
            have hbm := (nat64MulChecked_correct base base).1 base' hbaseSq
            have hinv' : acc'.toNat * base'.toNat ^ (nat64Shr exp (1, 0)).toNat = target := by
              rw [hbm, hshr]; exact hStep
            have hnz' : base'.toNat = 0 ∨ 1 ≤ acc'.toNat := by
              rcases hacc_nz with hbz | hacc1
              · left; rw [hbm, hbz, Nat.mul_zero]
              · exact Or.inr hacc1
            exact nat64PowAux_correct fuel acc' base' (nat64Shr exp (1, 0)) target
              hexp'_lt hinv' hnz'

/-- **Theorem (`nat64PowChecked_correct`)**:
    Checked 64-bit exponentiation `nat64PowChecked a b` returns `some r` with
    `r.toNat = a.toNat ^ b.toNat` whenever `< 2^64`, and delegates (`none`) iff
    `a.toNat ^ b.toNat ≥ 2^64`. -/
theorem nat64PowChecked_correct (a b : Nat64) :
    (∀ r, nat64PowChecked a b = some r -> r.toNat = a.toNat ^ b.toNat) ∧
    (nat64PowChecked a b = none -> 2 ^ 64 ≤ a.toNat ^ b.toNat) := by
  unfold nat64PowChecked
  exact nat64PowAux_correct 64 (1, 0) a b (a.toNat ^ b.toNat)
    (nat64_toNat_lt b) (by simp [Nat64.toNat]) (Or.inr (by simp [Nat64.toNat]))

/-- Fuel-bounded 64-bit Euclidean GCD loop; returns `none` on fuel exhaustion (host delegation). -/
def nat64GcdLoop : Nat -> Nat64 -> Nat64 -> Option Nat64
  | 0, a, b => if nat64IsZero b then some a else none
  | fuel + 1, a, b =>
    if nat64IsZero b then some a
    else nat64GcdLoop fuel b (nat64Mod a b)

/-- Bounded 64-bit Euclidean GCD (`none` triggers host delegation). -/
def nat64Gcd (fuel : Nat) (a b : Nat64) : Option Nat64 :=
  nat64GcdLoop fuel a b

/-- **Theorem (`nat64Gcd_correct`)**:
    Whenever `nat64Gcd fuel a b` succeeds with `some g` (without delegating),
    `g.toNat = Nat.gcd a.toNat b.toNat`. -/
theorem nat64Gcd_correct :
    ∀ (fuel : Nat) (a b g : Nat64),
      nat64Gcd fuel a b = some g ->
      g.toNat = Nat.gcd a.toNat b.toNat
  | 0, a, b, g, h => by
    unfold nat64Gcd nat64GcdLoop at h
    by_cases hbz : b.toNat = 0
    · have hiz : nat64IsZero b = true := (nat64IsZero_iff b).mpr hbz
      simp only [hiz, ↓reduceIte, Option.some.injEq] at h
      rw [← h, hbz, Nat.gcd_zero_right]
    · have hizf : nat64IsZero b = false := by
        cases hc : nat64IsZero b
        · rfl
        · exfalso; exact hbz ((nat64IsZero_iff b).mp hc)
      simp [hizf] at h
  | fuel + 1, a, b, g, h => by
    unfold nat64Gcd nat64GcdLoop at h
    by_cases hbz : b.toNat = 0
    · have hiz : nat64IsZero b = true := (nat64IsZero_iff b).mpr hbz
      simp only [hiz, ↓reduceIte, Option.some.injEq] at h
      rw [← h, hbz, Nat.gcd_zero_right]
    · have hizf : nat64IsZero b = false := by
        cases hc : nat64IsZero b
        · rfl
        · exfalso; exact hbz ((nat64IsZero_iff b).mp hc)
      simp only [hizf, Bool.false_eq_true, ↓reduceIte] at h
      have ih := nat64Gcd_correct fuel b (nat64Mod a b) g h
      have hmod : (nat64Mod a b).toNat = a.toNat % b.toNat := by
        rw [nat64Mod_correct a b]
        simp [hbz]
      rw [ih, hmod, Nat.gcd_comm, ← Nat.gcd_rec]
      exact Nat.gcd_comm b.toNat a.toNat

/-! ### 3. Universe-Aware Spine Expressions, Speculative Same-Head Congruence, and 0-Field Eta -/

/-- Constant reducibility hints in the GPU constant table (`ReducibilityHint`). -/
inductive ReducibilityHint where
  | opaqueHint
  | abbrevHint
  | regularHint
  deriving DecidableEq, Repr, Inhabited

/-- Universe-polymorphic kernel expression syntax for speculative spine and structure eta. -/
inductive SExpr where
  | bvar (idx : Nat)
  | fvar (id : Nat)
  | sort (lvl : Nat)
  | const (cid : Nat) (us : List Nat)
  | app (fn arg : SExpr)
  | lam (dom body : SExpr)
  | forallE (dom cod : SExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Multi-argument spine builder `sMkAppN f [a₁, ..., aₙ] = (...((f a₁) a₂) ... aₙ)`. -/
def sMkAppN (fn : SExpr) (args : List SExpr) : SExpr :=
  args.foldl SExpr.app fn

/-- Constant declaration with reducibility hint and optional closed unfolding body. -/
structure SDecl where
  ty : SExpr
  val? : Option SExpr
  hint : ReducibilityHint
  deriving DecidableEq, Repr, Inhabited

/-- Zero-field single-constructor structure descriptor (e.g. `Unit`, `PUnit`, non-`Prop`). -/
structure ZeroFieldStructSpec where
  structCid : Nat
  ctorCid : Nat
  numParams : Nat
  numFields : Nat
  allowsEta : Bool
  isProp : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Predicate identifying a sound 0-field single-constructor `eta` structure (`¬ isProp`). -/
def ZeroFieldEtaEligible (sd : ZeroFieldStructSpec) : Prop :=
  sd.allowsEta = true ∧ sd.isProp = false ∧ sd.numFields = 0

/-- Universe-aware environment: constant declarations + registered structure specs. -/
structure SEnv where
  decls : Array SDecl
  structs : List ZeroFieldStructSpec
  deriving Repr, Inhabited

mutual
  /-- Declarative kernel definitional equality supporting constant unfolding (for non-`opaqueHint`
      or delta fallback), congruence across any hint, and 0-field non-`Prop` structure eta. -/
  inductive SDefEq (env : SEnv) : SExpr -> SExpr -> Prop
    | refl (a : SExpr) : SDefEq env a a
    | symm {a b : SExpr} : SDefEq env a b -> SDefEq env b a
    | trans {a b c : SExpr} : SDefEq env a b -> SDefEq env b c -> SDefEq env a c
    | app {f₁ f₂ a₁ a₂ : SExpr} :
        SDefEq env f₁ f₂ -> SDefEq env a₁ a₂ -> SDefEq env (.app f₁ a₁) (.app f₂ a₂)
    | lam {d₁ d₂ b₁ b₂ : SExpr} :
        SDefEq env d₁ d₂ -> SDefEq env b₁ b₂ -> SDefEq env (.lam d₁ b₁) (.lam d₂ b₂)
    | forallE {d₁ d₂ c₁ c₂ : SExpr} :
        SDefEq env d₁ d₂ -> SDefEq env c₁ c₂ -> SDefEq env (.forallE d₁ c₁) (.forallE d₂ c₂)
    | delta {cid : Nat} {us : List Nat} {d : SDecl} {body : SExpr} :
        env.decls[cid]? = some d ->
        d.hint ≠ .opaqueHint ->
        d.val? = some body ->
        SDefEq env (.const cid us) body
    | structEtaZero {ctx : List SExpr} {sd : ZeroFieldStructSpec}
        {t : SExpr} {us : List Nat} {params : List SExpr} :
        sd ∈ env.structs ->
        ZeroFieldEtaEligible sd ->
        params.length = sd.numParams ->
        SHasType env ctx t (sMkAppN (.const sd.structCid us) params) ->
        SDefEq env t (sMkAppN (.const sd.ctorCid us) params)

  /-- Declarative typing judgment paired with `SDefEq` conversion for 0-field eta soundness. -/
  inductive SHasType (env : SEnv) : List SExpr -> SExpr -> SExpr -> Prop
    | bvar {ctx idx ty} : ctx[idx]? = some ty -> SHasType env ctx (.bvar idx) ty
    | fvar {ctx id ty} : SHasType env ctx (.fvar id) ty
    | sort {ctx lvl} : SHasType env ctx (.sort lvl) (.sort (lvl + 1))
    | const {ctx cid us d} :
        env.decls[cid]? = some d ->
        SHasType env ctx (.const cid us) d.ty
    | app {ctx f a dom cod} :
        SHasType env ctx f (.forallE dom cod) ->
        SHasType env ctx a dom ->
        SHasType env ctx (.app f a) cod
    | conv {ctx e T₁ T₂ u} :
        SHasType env ctx e T₁ ->
        SDefEq env T₁ T₂ ->
        SHasType env ctx T₂ (.sort u) ->
        SHasType env ctx e T₂
end

/-- Pairwise list relation over two lists of equal length. -/
inductive ListRel {α : Type} (R : α -> α -> Prop) : List α -> List α -> Prop
  | nil : ListRel R [] []
  | cons {a b : α} {as bs : List α} : R a b -> ListRel R as bs -> ListRel R (a :: as) (b :: bs)

theorem sMkAppN_congr {env : SEnv} :
    ∀ {f₁ f₂ : SExpr} {args₁ args₂ : List SExpr},
      SDefEq env f₁ f₂ ->
      ListRel (SDefEq env) args₁ args₂ ->
      SDefEq env (sMkAppN f₁ args₁) (sMkAppN f₂ args₂)
  | _, _, _, _, hf, .nil => hf
  | _, _, _, _, hf, .cons ha hrest => by
    simp only [sMkAppN, List.foldl_cons] at *
    exact sMkAppN_congr (.app hf ha) hrest

/-- Recursive pairwise Boolean argument checker corresponding to `OP_DEFEQ_SPINE`. -/
def spineArgsCheck (argEq : SExpr -> SExpr -> Bool) : List SExpr -> List SExpr -> Bool
  | [], [] => true
  | a :: ar, b :: br => argEq a b && spineArgsCheck argEq ar br
  | _, _ => false

/-- Speculative same-head spine check (`OP_DEFEQ_SPINE`) comparing `(c₁, us₁)` vs `(c₂, us₂)`
    and pairwise arguments via `argEq`. Returns `false` on any mismatch to fall back to
    delta unfolding / stuck checks. -/
def speculativeSpineCheck (argEq : SExpr -> SExpr -> Bool)
    (c₁ : Nat) (us₁ : List Nat) (args₁ : List SExpr)
    (c₂ : Nat) (us₂ : List Nat) (args₂ : List SExpr) : Bool :=
  (c₁ == c₂) && (us₁ == us₂) && spineArgsCheck argEq args₁ args₂

/-- Speculative same-head spine check followed by delta/stuck fallback on `false`. -/
def spineWithFallback (argEq : SExpr -> SExpr -> Bool)
    (fallback : SExpr -> SExpr -> Bool)
    (c₁ : Nat) (us₁ : List Nat) (args₁ : List SExpr)
    (c₂ : Nat) (us₂ : List Nat) (args₂ : List SExpr) : Bool :=
  if speculativeSpineCheck argEq c₁ us₁ args₁ c₂ us₂ args₂ then true
  else fallback (sMkAppN (.const c₁ us₁) args₁) (sMkAppN (.const c₂ us₂) args₂)

private theorem spineArgsCheck_sound {env : SEnv} {argEq : SExpr -> SExpr -> Bool}
    (harg : ∀ a b, argEq a b = true -> SDefEq env a b) :
    ∀ {args₁ args₂ : List SExpr},
      spineArgsCheck argEq args₁ args₂ = true ->
      ListRel (SDefEq env) args₁ args₂
  | [], [], _ => ListRel.nil
  | _ :: _, [], h => by simp [spineArgsCheck] at h
  | [], _ :: _, h => by simp [spineArgsCheck] at h
  | a :: ar, b :: br, h => by
    simp only [spineArgsCheck, Bool.and_eq_true] at h
    exact ListRel.cons (harg a b h.1) (spineArgsCheck_sound harg h.2)

/-- **Theorem (`sameHeadSpine_defeq_sound`)**:
    For matching constant heads `(c₁, us₁)` vs `(c₂, us₂)` regardless of `ReducibilityHint`
    (`opaqueHint`, `abbrevHint`, `regularHint`):
    1. Equal constant IDs, equal universe level lists, and pairwise `SDefEq` arguments
       imply `SDefEq env` on the full `sMkAppN` applications.
    2. Whenever `speculativeSpineCheck` returns `true`, `SDefEq env` holds.
    3. Returning `false` from `speculativeSpineCheck` and falling back to a sound delta/stuck
       checker `fallback` never accepts an invalid equality. -/
theorem sameHeadSpine_defeq_sound (env : SEnv)
    (hint₁ hint₂ : ReducibilityHint)
    (argEq : SExpr -> SExpr -> Bool)
    (fallback : SExpr -> SExpr -> Bool)
    (harg : ∀ a b, argEq a b = true -> SDefEq env a b)
    (hfb : ∀ x y, fallback x y = true -> SDefEq env x y)
    (c₁ c₂ : Nat) (us₁ us₂ : List Nat) (args₁ args₂ : List SExpr) :
    (c₁ = c₂ -> us₁ = us₂ -> ListRel (SDefEq env) args₁ args₂ ->
      SDefEq env (sMkAppN (.const c₁ us₁) args₁) (sMkAppN (.const c₂ us₂) args₂)) ∧
    (speculativeSpineCheck argEq c₁ us₁ args₁ c₂ us₂ args₂ = true ->
      SDefEq env (sMkAppN (.const c₁ us₁) args₁) (sMkAppN (.const c₂ us₂) args₂)) ∧
    (spineWithFallback argEq fallback c₁ us₁ args₁ c₂ us₂ args₂ = true ->
      SDefEq env (sMkAppN (.const c₁ us₁) args₁) (sMkAppN (.const c₂ us₂) args₂)) := by
  have _ := (hint₁, hint₂)
  have h1 : c₁ = c₂ -> us₁ = us₂ -> ListRel (SDefEq env) args₁ args₂ ->
      SDefEq env (sMkAppN (.const c₁ us₁) args₁) (sMkAppN (.const c₂ us₂) args₂) := by
    intro hc hus hargs
    subst hc; subst hus
    exact sMkAppN_congr (.refl (.const c₁ us₁)) hargs
  have h2 : speculativeSpineCheck argEq c₁ us₁ args₁ c₂ us₂ args₂ = true ->
      SDefEq env (sMkAppN (.const c₁ us₁) args₁) (sMkAppN (.const c₂ us₂) args₂) := by
    intro hsp
    unfold speculativeSpineCheck at hsp
    simp only [Bool.and_eq_true, beq_iff_eq] at hsp
    exact h1 hsp.1.1 hsp.1.2 (spineArgsCheck_sound harg hsp.2)
  refine ⟨h1, h2, ?_⟩
  intro hwf
  unfold spineWithFallback at hwf
  split at hwf
  · next hsp => exact h2 hsp
  · exact hfb _ _ hwf

/-- Guarded runtime check implementing 0-field single-constructor non-`Prop` eta congruence. -/
def tryZeroFieldEtaCheck (sd : ZeroFieldStructSpec) (inEnv : Bool)
    (_us₁ _us₂ : List Nat) (params₁ params₂ : List SExpr)
    (typesDefEq : Bool) : Bool :=
  inEnv &&
  sd.allowsEta &&
  !sd.isProp &&
  (sd.numFields == 0) &&
  (params₁.length == sd.numParams) &&
  (params₂.length == sd.numParams) &&
  typesDefEq

/-- **Theorem (`zeroFieldEta_defeq_sound`)**:
    For any 0-field single-constructor `eta` structure (`isProp = false`, `numFields = 0`,
    `allowsEta = true`) registered in `env.structs`, any two terms `x` and `y` having
    definitionally equal well-typed applied structure types `sMkAppN (.const sd.structCid us₁) params₁`
    and `sMkAppN (.const sd.structCid us₂) params₂` are definitionally equal (`SDefEq env x y`),
    matching `Unit` / `PUnit` eta soundness; furthermore `tryZeroFieldEtaCheck = true` guarantees `SDefEq`. -/
theorem zeroFieldEta_defeq_sound {env : SEnv} {ctx : List SExpr}
    {sd : ZeroFieldStructSpec}
    {x y : SExpr} {us₁ us₂ : List Nat} {params₁ params₂ : List SExpr} {u₁ : Nat}
    (hsd : sd ∈ env.structs)
    (helig : ZeroFieldEtaEligible sd)
    (hp₁ : params₁.length = sd.numParams)
    (hp₂ : params₂.length = sd.numParams)
    (hx : SHasType env ctx x (sMkAppN (.const sd.structCid us₁) params₁))
    (hy : SHasType env ctx y (sMkAppN (.const sd.structCid us₂) params₂))
    (hT₁ : SHasType env ctx (sMkAppN (.const sd.structCid us₁) params₁) (.sort u₁))
    (hTeq : SDefEq env (sMkAppN (.const sd.structCid us₁) params₁)
        (sMkAppN (.const sd.structCid us₂) params₂)) :
    SDefEq env x y := by
  have hy' : SHasType env ctx y (sMkAppN (.const sd.structCid us₁) params₁) :=
    .conv hy (.symm hTeq) hT₁
  have hxEta : SDefEq env x (sMkAppN (.const sd.ctorCid us₁) params₁) :=
    .structEtaZero hsd helig hp₁ hx
  have hyEta : SDefEq env y (sMkAppN (.const sd.ctorCid us₁) params₁) :=
    .structEtaZero hsd helig hp₁ hy'
  have _ := hp₂
  exact .trans hxEta (.symm hyEta)

/-- Boolean-guarded variant verifying that `tryZeroFieldEtaCheck` rejects `Prop`, non-eta,
    or mismatched-field structures and only accepts sound `SDefEq` pairs. -/
theorem zeroFieldEtaCheck_sound {env : SEnv} {ctx : List SExpr}
    {sd : ZeroFieldStructSpec} {x y : SExpr} {us₁ us₂ : List Nat}
    {params₁ params₂ : List SExpr} {u₁ : Nat} {typesDefEq : Bool}
    (hin : sd ∈ env.structs)
    (hx : SHasType env ctx x (sMkAppN (.const sd.structCid us₁) params₁))
    (hy : SHasType env ctx y (sMkAppN (.const sd.structCid us₂) params₂))
    (hT₁ : SHasType env ctx (sMkAppN (.const sd.structCid us₁) params₁) (.sort u₁))
    (htypes : typesDefEq = true ->
      SDefEq env (sMkAppN (.const sd.structCid us₁) params₁)
        (sMkAppN (.const sd.structCid us₂) params₂))
    (hchk : tryZeroFieldEtaCheck sd true us₁ us₂ params₁ params₂ typesDefEq = true) :
    SDefEq env x y := by
  unfold tryZeroFieldEtaCheck at hchk
  simp only [Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨ha, hnp⟩, hnf⟩, hp1⟩, hp2⟩, hde⟩
  exact zeroFieldEta_defeq_sound hin ⟨ha, hnp, hnf⟩ hp1 hp2 hx hy hT₁ (htypes hde)

/-! ### 4. Phase 3 Epoch-Tagged `(a, b, depth, job_epoch)` `DEFEQ` Memo Soundness -/

/-- Key for the per-lane Phase 3 `DEFEQ` cache (`(a, b, depth)`). -/
structure DefEqMemoKey where
  a : EIdx
  b : EIdx
  depth : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Conclusive `DEFEQ` verdict stored in cache (`eqTrue` or `eqFalse`). Halted / delegated
    outcomes are never representable as cached verdicts. -/
inductive DefEqVerdict where
  | eqTrue
  | eqFalse
  deriving DecidableEq, Repr, Inhabited

/-- Full runtime outcome of a bounded `DEFEQ` query: conclusive Boolean or halted/delegated. -/
inductive DefEqOutcome where
  | conclusive (ok : Bool)
  | halted
  deriving DecidableEq, Repr, Inhabited

/-- Epoch-stamped `(a, b, depth, epoch)` `DEFEQ` cache slot. -/
structure DefEqMemoEntry where
  epoch : Nat
  key : DefEqMemoKey
  verdict : DefEqVerdict
  deriving DecidableEq, Repr, Inhabited

abbrev DefEqMemoTable := Array (Option DefEqMemoEntry)

/-- State of an epoch-tagged `DEFEQ` cache across sequential jobs on a GPU lane. -/
structure DefEqLaneMemo where
  scr : SoATier
  epoch : Nat
  table : DefEqMemoTable
  slotOf : DefEqMemoKey -> Nat

/-- Epoch-guarded `DEFEQ` cache lookup; entries with `entry.epoch ≠ curEpoch` are treated as
    cache misses without zeroing the table between jobs. -/
def defeqMemoLookup (curEpoch : Nat) (tbl : DefEqMemoTable)
    (slotOf : DefEqMemoKey -> Nat) (key : DefEqMemoKey) : Option DefEqVerdict :=
  match tbl[slotOf key]? with
  | some (some entry) =>
    if entry.epoch == curEpoch && entry.key == key then some entry.verdict else none
  | _ => none

/-- Conditional insertion: writes ONLY conclusive verdicts (`eqTrue`/`eqFalse`); halted runs
    never populate the memo table. -/
def defeqMemoInsert (curEpoch : Nat) (tbl : DefEqMemoTable)
    (slotOf : DefEqMemoKey -> Nat) (key : DefEqMemoKey) (out : DefEqOutcome) : DefEqMemoTable :=
  match out with
  | .halted => tbl
  | .conclusive ok =>
    let slot := slotOf key
    let v := if ok then DefEqVerdict.eqTrue else DefEqVerdict.eqFalse
    if h : slot < tbl.size then
      tbl.set slot (some { epoch := curEpoch, key := key, verdict := v })
    else
      tbl

/-- Advance to the next sequential job on the same GPU lane: increments `epoch` and resets
    `scr := .empty` without an O(N) clear of `table`. -/
def advanceDefEqEpoch (lane : DefEqLaneMemo) : DefEqLaneMemo :=
  { lane with scr := SoATier.empty, epoch := lane.epoch + 1 }

/-- Semantic validity of a cached `(a, b, depth)` verdict against `(env, pers, scr)`. -/
def DefEqMemoEntryValid (env : KEnv) (pers scr : SoATier)
    (key : DefEqMemoKey) (v : DefEqVerdict) : Prop :=
  ∃ ka kb, Interprets pers scr key.a ka ∧ Interprets pers scr key.b kb ∧
    match v with
    | .eqTrue => ∃ f, defEqSpec env f key.depth ka kb = true
    | .eqFalse => ∀ f, defEqSpec env f key.depth ka kb = false

/-- Outcome validity for runtime insertion; `.halted` imposes no false-conclusive obligation. -/
def DefEqOutcomeValid (env : KEnv) (pers scr : SoATier)
    (key : DefEqMemoKey) (out : DefEqOutcome) : Prop :=
  match out with
  | .halted => True
  | .conclusive true => DefEqMemoEntryValid env pers scr key .eqTrue
  | .conclusive false => DefEqMemoEntryValid env pers scr key .eqFalse

/-- Table invariant: every populated slot satisfies `entry.epoch ≤ curEpoch`, and any slot
    matching `curEpoch` stores a valid conclusive `(key, verdict)` wrt `(env, pers, scr)`. -/
def DefEqMemoInv (env : KEnv) (pers scr : SoATier) (curEpoch : Nat)
    (tbl : DefEqMemoTable) : Prop :=
  ∀ (slot : Nat) (entry : DefEqMemoEntry), tbl[slot]? = some (some entry) ->
    entry.epoch ≤ curEpoch ∧
    (entry.epoch = curEpoch -> DefEqMemoEntryValid env pers scr entry.key entry.verdict)

theorem defeqMemoInsert_preserves_inv {env : KEnv} {pers scr : SoATier} {curEpoch : Nat}
    {tbl : DefEqMemoTable} {slotOf : DefEqMemoKey -> Nat} {key : DefEqMemoKey}
    {out : DefEqOutcome}
    (hinv : DefEqMemoInv env pers scr curEpoch tbl)
    (hout : DefEqOutcomeValid env pers scr key out) :
    DefEqMemoInv env pers scr curEpoch (defeqMemoInsert curEpoch tbl slotOf key out) := by
  cases out with
  | halted =>
    simpa [defeqMemoInsert] using hinv
  | conclusive ok =>
    unfold defeqMemoInsert
    dsimp only
    by_cases hs : slotOf key < tbl.size
    · simp only [hs, ↓reduceDIte]
      intro slot entry hlu
      let v := if ok then DefEqVerdict.eqTrue else DefEqVerdict.eqFalse
      by_cases heq : slot = slotOf key
      · subst heq
        have hsz : slotOf key <
            (tbl.set (slotOf key) (some { epoch := curEpoch, key := key, verdict := v })).size := by
          rw [Array.size_set]; exact hs
        rw [Array.getElem?_eq_getElem hsz, Array.getElem_set_self,
          Option.some.injEq, Option.some.injEq] at hlu
        subst hlu
        refine ⟨Nat.le_refl _, fun _ => ?_⟩
        cases ok
        · simpa [DefEqOutcomeValid, v] using hout
        · simpa [DefEqOutcomeValid, v] using hout
      · have hget :
            (tbl.set (slotOf key) (some { epoch := curEpoch, key := key, verdict := v }))[slot]? =
              tbl[slot]? := by
          by_cases hlt : slot < tbl.size
          · have hsz : slot <
                (tbl.set (slotOf key) (some { epoch := curEpoch, key := key, verdict := v })).size := by
              rw [Array.size_set]; exact hlt
            rw [Array.getElem?_eq_getElem hsz, Array.getElem?_eq_getElem hlt,
              Array.getElem_set_ne hs hlt (Ne.symm heq)]
          · have hsz :
                (tbl.set (slotOf key) (some { epoch := curEpoch, key := key, verdict := v })).size ≤ slot := by
              rw [Array.size_set]; exact Nat.le_of_not_lt hlt
            rw [Array.getElem?_eq_none hsz, Array.getElem?_eq_none (Nat.le_of_not_lt hlt)]
        rw [hget] at hlu
        exact hinv slot entry hlu
    · simp only [hs, ↓reduceDIte]
      exact hinv

theorem defeqMemoInv_extends {env : KEnv} {pers scr scr' : SoATier} {curEpoch : Nat}
    {tbl : DefEqMemoTable} (hex : TierExtends scr scr')
    (hinv : DefEqMemoInv env pers scr curEpoch tbl) :
    DefEqMemoInv env pers scr' curEpoch tbl := by
  intro slot entry hlu
  obtain ⟨hle, hv⟩ := hinv slot entry hlu
  refine ⟨hle, fun heq => ?_⟩
  rcases hv heq with ⟨ka, kb, ha, hb, hres⟩
  exact ⟨ka, kb, interprets_extends hex ha, interprets_extends hex hb, hres⟩

/-- **Theorem (`defeqEpochMemo_hit_sound`)**:
    Under `DefEqMemoInv`, every hit `defeqMemoLookup curEpoch tbl slotOf key = some verdict`
    corresponds to decoded terms `ka, kb` where `.eqTrue` guarantees `∃ f, defEqSpec env f key.depth ka kb = true`
    and `.eqFalse` guarantees `∀ f, defEqSpec env f key.depth ka kb = false`.
    Halted runs never modify the cache and stale epochs are never returned. -/
theorem defeqEpochMemo_hit_sound {env : KEnv} {pers scr : SoATier} {curEpoch : Nat}
    {tbl : DefEqMemoTable} {slotOf : DefEqMemoKey -> Nat} {key : DefEqMemoKey}
    {verdict : DefEqVerdict}
    (hinv : DefEqMemoInv env pers scr curEpoch tbl)
    (hl : defeqMemoLookup curEpoch tbl slotOf key = some verdict) :
    DefEqMemoEntryValid env pers scr key verdict := by
  unfold defeqMemoLookup at hl
  cases hs : tbl[slotOf key]? with
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

/-- **Theorem (`advanceEpoch_preserves_defeqMemo`)**:
    Advancing `epoch := epoch + 1` and resetting `scr := .empty` between sequential jobs on a
    GPU lane preserves `DefEqMemoInv` without touching any table entry, and guarantees every
    previously cached slot yields a cache miss (`none`) in the new epoch. -/
theorem advanceEpoch_preserves_defeqMemo {env : KEnv} {pers : SoATier}
    (lane : DefEqLaneMemo)
    (hinv : DefEqMemoInv env pers lane.scr lane.epoch lane.table) :
    DefEqMemoInv env pers SoATier.empty (advanceDefEqEpoch lane).epoch (advanceDefEqEpoch lane).table ∧
    (∀ key : DefEqMemoKey,
      defeqMemoLookup (advanceDefEqEpoch lane).epoch (advanceDefEqEpoch lane).table lane.slotOf key = none) := by
  unfold advanceDefEqEpoch
  dsimp only
  refine ⟨?_, ?_⟩
  · intro slot entry hlu
    obtain ⟨hle, _⟩ := hinv slot entry hlu
    exact ⟨Nat.le_succ_of_le hle, fun h => by omega⟩
  · intro key
    unfold defeqMemoLookup
    cases hs : lane.table[lane.slotOf key]? with
    | none => rfl
    | some m =>
      cases m with
      | none => rfl
      | some entry =>
        have hle := (hinv (lane.slotOf key) entry hs).1
        have hne : (entry.epoch == lane.epoch + 1) = false := beq_false_of_ne (by omega)
        simp [hne]

/-! ### 5. Two-Ended Hybrid GPU/CPU Work-Stealing & `CGSNAP02` Dual Snapshot Restoration -/

/-- Minimum failing index in `[lo, hi)` according to `isValid`, or `none` if all pass. -/
def minFailInRange (isValid : Nat -> Bool) (lo hi : Nat) : Option Nat :=
  let rec go : Nat -> Nat -> Option Nat
    | 0, _ => none
    | rem + 1, cur =>
      if isValid cur then go rem (cur + 1) else some cur
  go (hi - lo) lo

/-- Combines two optional failing indices by taking the smaller index (`none` = identity). -/
def optMinNat : Option Nat -> Option Nat -> Option Nat
  | none, y => y
  | x, none => x
  | some a, some b => some (Nat.min a b)

private theorem optMinNat_none_right (x : Option Nat) : optMinNat x none = x := by
  cases x <;> rfl

private theorem optMinNat_assoc (x y z : Option Nat) :
    optMinNat (optMinNat x y) z = optMinNat x (optMinNat y z) := by
  cases x <;> cases y <;> cases z <;> simp [optMinNat, Nat.min_assoc]

private theorem minFailInRange_go_eq_none (isValid : Nat -> Bool) :
    ∀ (rem cur : Nat),
      minFailInRange.go isValid rem cur = none ↔
      (∀ i, cur ≤ i -> i < cur + rem -> isValid i = true)
  | 0, cur => by
    simp only [minFailInRange.go, Nat.add_zero]
    exact ⟨fun _ _ h1 h2 => by omega, fun _ => trivial⟩
  | rem + 1, cur => by
    unfold minFailInRange.go
    by_cases hv : isValid cur = true
    · simp only [hv, ↓reduceIte]
      have ih := minFailInRange_go_eq_none isValid rem (cur + 1)
      constructor
      · intro h i h1 h2
        by_cases heq : i = cur
        · rw [heq]; exact hv
        · exact ih.mp h i (by omega) (by omega)
      · intro hall
        exact ih.mpr (fun i h1 h2 => hall i (by omega) (by omega))
    · have hvf : isValid cur = false := Bool.eq_false_iff.mpr hv
      simp only [hvf, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; cases h
      · intro hall
        exfalso
        exact hv (hall cur (Nat.le_refl _) (by omega))

private theorem minFailInRange_go_eq_some (isValid : Nat -> Bool) :
    ∀ (rem cur k : Nat),
      minFailInRange.go isValid rem cur = some k ↔
      (cur ≤ k ∧ k < cur + rem ∧ isValid k = false ∧
       ∀ j, cur ≤ j -> j < k -> isValid j = true)
  | 0, cur, k => by
    simp only [minFailInRange.go, Nat.add_zero]
    exact ⟨(fun h => by cases h), (fun ⟨h1, h2, _⟩ => by omega)⟩
  | rem + 1, cur, k => by
    unfold minFailInRange.go
    by_cases hv : isValid cur = true
    · simp only [hv, ↓reduceIte]
      have ih := minFailInRange_go_eq_some isValid rem (cur + 1) k
      constructor
      · intro h
        obtain ⟨h1, h2, hkf, hprev⟩ := ih.mp h
        refine ⟨by omega, by omega, hkf, fun j hj1 hj2 => ?_⟩
        by_cases heq : j = cur
        · rw [heq]; exact hv
        · exact hprev j (by omega) hj2
      · intro ⟨_, hk2, hkf, hprev⟩
        have hne : k ≠ cur := by
          intro hkc; rw [hkc, hv] at hkf; cases hkf
        exact ih.mpr ⟨by omega, by omega, hkf, fun j hj1 hj2 => hprev j (by omega) hj2⟩
    · have hvf : isValid cur = false := Bool.eq_false_iff.mpr hv
      simp only [hvf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      constructor
      · intro h
        rw [← h]
        exact ⟨Nat.le_refl _, by omega, hvf, fun j hj1 hj2 => by omega⟩
      · intro ⟨h1, _, hkf, hprev⟩
        by_cases heq : cur = k
        · exact heq
        · exfalso
          have hcurt := hprev cur (Nat.le_refl _) (by omega)
          rw [hvf] at hcurt; cases hcurt

private theorem minFailInRange_self (isValid : Nat -> Bool) (k : Nat) :
    minFailInRange isValid k k = none := by
  unfold minFailInRange
  rw [Nat.sub_self]
  rfl

private theorem minFailInRange_snoc (isValid : Nat -> Bool) {lo mid : Nat} (hle : lo ≤ mid) :
    minFailInRange isValid lo (mid + 1) =
      optMinNat (minFailInRange isValid lo mid) (if isValid mid then none else some mid) := by
  unfold minFailInRange
  have hsub : mid + 1 - lo = (mid - lo) + 1 := by omega
  cases hpre : minFailInRange.go isValid (mid - lo) lo with
  | none =>
    have hall := (minFailInRange_go_eq_none isValid (mid - lo) lo).mp hpre
    have hpre' : ∀ i, lo ≤ i -> i < lo + (mid - lo) -> isValid i = true := hall
    by_cases hv : isValid mid = true
    · simp only [hv, ↓reduceIte, optMinNat]
      rw [hsub]
      exact (minFailInRange_go_eq_none isValid ((mid - lo) + 1) lo).mpr
        (fun i h1 h2 => by
          by_cases him : i = mid
          · rw [him]; exact hv
          · exact hpre' i h1 (by omega))
    · have hvf : isValid mid = false := Bool.eq_false_iff.mpr hv
      simp only [hvf, Bool.false_eq_true, ↓reduceIte, optMinNat]
      rw [hsub]
      exact (minFailInRange_go_eq_some isValid ((mid - lo) + 1) lo mid).mpr
        ⟨hle, by omega, hvf, fun j hj1 hj2 => hpre' j hj1 (by omega)⟩
  | some k =>
    have hsome := (minFailInRange_go_eq_some isValid (mid - lo) lo k).mp hpre
    have hk_lt : k < mid := by omega
    have hres : minFailInRange.go isValid (mid + 1 - lo) lo = some k := by
      rw [hsub]
      exact (minFailInRange_go_eq_some isValid ((mid - lo) + 1) lo k).mpr
        ⟨hsome.1, by omega, hsome.2.2.1, hsome.2.2.2⟩
    rw [hres]
    by_cases hv : isValid mid = true
    · simp only [hv, ↓reduceIte, optMinNat]
    · have hvf : isValid mid = false := Bool.eq_false_iff.mpr hv
      simp only [hvf, Bool.false_eq_true, ↓reduceIte, optMinNat, Option.some.injEq]
      exact (Nat.min_eq_left (Nat.le_of_lt hk_lt)).symm

private theorem minFailInRange_cons (isValid : Nat -> Bool) {mid hi : Nat} (hlt : mid < hi) :
    minFailInRange isValid mid hi =
      optMinNat (if isValid mid then none else some mid) (minFailInRange isValid (mid + 1) hi) := by
  unfold minFailInRange
  have hsub : hi - mid = (hi - (mid + 1)) + 1 := by omega
  rw [hsub, minFailInRange.go]
  by_cases hv : isValid mid = true
  · simp [hv, optMinNat]
  · have hvf : isValid mid = false := Bool.eq_false_iff.mpr hv
    simp only [hvf, Bool.false_eq_true, ↓reduceIte]
    cases hsuf : minFailInRange.go isValid (hi - (mid + 1)) (mid + 1) with
    | none => simp [optMinNat]
    | some k =>
      have hsome := (minFailInRange_go_eq_some isValid (hi - (mid + 1)) (mid + 1) k).mp hsuf
      simp only [optMinNat, Option.some.injEq]
      exact (Nat.min_eq_left (by omega)).symm

private theorem minFailInRange_split (isValid : Nat -> Bool) {lo mid hi : Nat}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    minFailInRange isValid lo hi =
      optMinNat (minFailInRange isValid lo mid) (minFailInRange isValid mid hi) := by
  have hrec : ∀ (d hi' : Nat), lo + d ≤ hi' ->
      minFailInRange isValid lo hi' =
        optMinNat (minFailInRange isValid lo (lo + d)) (minFailInRange isValid (lo + d) hi') := by
    intro d
    induction d with
    | zero =>
      intro hi' _
      rw [Nat.add_zero, minFailInRange_self, optMinNat]
    | succ d ih =>
      intro hi' hle'
      have hle_prev : lo + d ≤ hi' := by omega
      have hlt' : lo + d < hi' := by omega
      have hbase := ih hi' hle_prev
      rw [hbase]
      have hadd1 : lo + (d + 1) = (lo + d) + 1 := by omega
      rw [hadd1]
      rw [minFailInRange_snoc isValid (by omega : lo ≤ lo + d)]
      rw [minFailInRange_cons isValid hlt']
      rw [optMinNat_assoc]
  have hr := hrec (mid - lo) hi (by omega)
  have hmid : lo + (mid - lo) = mid := Nat.add_sub_of_le h1
  rw [hmid] at hr
  exact hr

/-- State of the two-ended GPU-front / CPU-back dynamic work-stealing queue over `[0..n)`. -/
structure HybridStealState where
  n : Nat
  gpuFront : Nat
  cpuBack : Nat
  gpuMinFail : Option Nat
  cpuMinFail : Option Nat
  deriving DecidableEq, Repr, Inhabited

/-- Initial work-stealing queue covering `[0..n)`. -/
def HybridStealState.init (n : Nat) : HybridStealState :=
  { n := n, gpuFront := 0, cpuBack := n, gpuMinFail := none, cpuMinFail := none }

/-- Atomic work-stealing action: GPU claims front `gpuFront`, or CPU steals back `cpuBack - 1`. -/
inductive StealStep where
  | gpuFront
  | cpuBack
  deriving DecidableEq, Repr, Inhabited

/-- Execute one atomic GPU-front or CPU-back claim against `isValid`. -/
def stepHybridSteal (isValid : Nat -> Bool) (st : HybridStealState) : StealStep -> HybridStealState
  | .gpuFront =>
    if st.gpuFront < st.cpuBack then
      let idx := st.gpuFront
      let fail? := if isValid idx then none else some idx
      { st with
        gpuFront := st.gpuFront + 1
        gpuMinFail := optMinNat st.gpuMinFail fail? }
    else st
  | .cpuBack =>
    if st.gpuFront < st.cpuBack then
      let idx := st.cpuBack - 1
      let fail? := if isValid idx then none else some idx
      { st with
        cpuBack := idx
        cpuMinFail := optMinNat fail? st.cpuMinFail }
    else st

/-- Run an arbitrary interleaved GPU/CPU work-stealing schedule. -/
def runHybridSteal (isValid : Nat -> Bool) (st : HybridStealState) (sched : List StealStep) :
    HybridStealState :=
  sched.foldl (stepHybridSteal isValid) st

/-- Combined minimum failure index `(gpuMinFail ⊓ cpuMinFail)` once `[0..n)` is partitioned. -/
def HybridStealState.combinedMinFail (st : HybridStealState) : Option Nat :=
  optMinNat st.gpuMinFail st.cpuMinFail

/-- Global acceptance decision of the two-ended hybrid queue (`true` iff no failure recorded). -/
def HybridStealState.accepted (st : HybridStealState) : Bool :=
  st.combinedMinFail.isNone

/-- Per-step partition & minimum-failure-index invariant of the two-ended queue. -/
def HybridStealInv (isValid : Nat -> Bool) (st : HybridStealState) : Prop :=
  st.gpuFront ≤ st.cpuBack ∧
  st.cpuBack ≤ st.n ∧
  st.gpuMinFail = minFailInRange isValid 0 st.gpuFront ∧
  st.cpuMinFail = minFailInRange isValid st.cpuBack st.n

theorem stepHybridSteal_preserves_inv (isValid : Nat -> Bool) (st : HybridStealState)
    (act : StealStep) (hinv : HybridStealInv isValid st) :
    HybridStealInv isValid (stepHybridSteal isValid st act) := by
  rcases hinv with ⟨hfc, hcn, hgf, hcb⟩
  cases act with
  | gpuFront =>
    unfold stepHybridSteal
    dsimp only
    by_cases hlt : st.gpuFront < st.cpuBack
    · simp only [hlt, ↓reduceIte]
      dsimp only [HybridStealInv]
      refine ⟨by omega, hcn, ?_, hcb⟩
      rw [hgf, ← minFailInRange_snoc isValid (Nat.zero_le _)]
    · simp only [hlt, ↓reduceIte]
      exact ⟨hfc, hcn, hgf, hcb⟩
  | cpuBack =>
    unfold stepHybridSteal
    dsimp only
    by_cases hlt : st.gpuFront < st.cpuBack
    · simp only [hlt, ↓reduceIte]
      dsimp only [HybridStealInv]
      have hpred : st.cpuBack - 1 < st.n := by omega
      have hsucc : (st.cpuBack - 1) + 1 = st.cpuBack := by omega
      refine ⟨by omega, by omega, hgf, ?_⟩
      have hcons := minFailInRange_cons isValid hpred
      rw [hsucc, ← hcb] at hcons
      exact hcons.symm
    · simp only [hlt, ↓reduceIte]
      exact ⟨hfc, hcn, hgf, hcb⟩

private theorem stepHybridSteal_preserves_n (isValid : Nat -> Bool) (st : HybridStealState)
    (act : StealStep) : (stepHybridSteal isValid st act).n = st.n := by
  cases act <;> unfold stepHybridSteal <;> dsimp only <;> split <;> rfl

private theorem runHybridSteal_preserves_n (isValid : Nat -> Bool) (sched : List StealStep) :
    ∀ st, (runHybridSteal isValid st sched).n = st.n := by
  induction sched with
  | nil => intro _; rfl
  | cons act rest ih =>
    intro st
    simp only [runHybridSteal, List.foldl_cons] at *
    rw [ih, stepHybridSteal_preserves_n]

theorem runHybridSteal_preserves_inv (isValid : Nat -> Bool) (sched : List StealStep) :
    ∀ st, HybridStealInv isValid st -> HybridStealInv isValid (runHybridSteal isValid st sched) := by
  induction sched with
  | nil => intro st h; exact h
  | cons act rest ih =>
    intro st h
    exact ih (stepHybridSteal isValid st act) (stepHybridSteal_preserves_inv isValid st act h)

/-- **Theorem (`twoEndedHybridSteal_sound`)**:
    For ANY interleaved schedule `sched` of front-GPU claims and back-CPU steals that drains
    `[0..n)` (`gpuFront = cpuBack`), the two sides partition `[0..n)` cleanly without overlap or gaps,
    `fin.accepted = true ↔ (∀ i < n, isValid i = true)`, and `fin.combinedMinFail` equals the exact
    minimum failure index `minFailInRange isValid 0 n`. -/
theorem twoEndedHybridSteal_sound (isValid : Nat -> Bool) (n : Nat) (sched : List StealStep)
    (hdrained : (runHybridSteal isValid (HybridStealState.init n) sched).gpuFront =
        (runHybridSteal isValid (HybridStealState.init n) sched).cpuBack) :
    let fin := runHybridSteal isValid (HybridStealState.init n) sched
    fin.combinedMinFail = minFailInRange isValid 0 n ∧
    (fin.accepted = true ↔ ∀ i, i < n -> isValid i = true) ∧
    (∀ k, fin.combinedMinFail = some k ->
      k < n ∧ isValid k = false ∧ ∀ j, j < k -> isValid j = true) := by
  have hinit : HybridStealInv isValid (HybridStealState.init n) := by
    refine ⟨Nat.zero_le _, Nat.le_refl _, ?_, ?_⟩
    · simp [HybridStealState.init, minFailInRange_self]
    · simp [HybridStealState.init, minFailInRange_self]
  have hfin := runHybridSteal_preserves_inv isValid sched (HybridStealState.init n) hinit
  have hn : (runHybridSteal isValid (HybridStealState.init n) sched).n = n :=
    runHybridSteal_preserves_n isValid sched (HybridStealState.init n)
  rcases hfin with ⟨hfc, hcn, hgf, hcb⟩
  rw [hn] at hcn hcb
  dsimp only
  have hmin : (runHybridSteal isValid (HybridStealState.init n) sched).combinedMinFail =
      minFailInRange isValid 0 n := by
    unfold HybridStealState.combinedMinFail
    rw [hgf, hcb, hdrained]
    exact (minFailInRange_split isValid (Nat.zero_le _) hcn).symm
  refine ⟨hmin, ?_, ?_⟩
  · unfold HybridStealState.accepted
    rw [hmin]
    unfold minFailInRange
    rw [Nat.sub_zero]
    constructor
    · intro hisnone i hi
      cases hgo : minFailInRange.go isValid n 0 with
      | none => exact (minFailInRange_go_eq_none isValid n 0).mp hgo i (Nat.zero_le _) (by omega)
      | some _ => rw [hgo] at hisnone; simp at hisnone
    · intro hall
      have hnone := (minFailInRange_go_eq_none isValid n 0).mpr (fun i _ hi => hall i (by omega))
      rw [hnone]; rfl
  · intro k hk
    rw [hmin] at hk
    unfold minFailInRange at hk
    rw [Nat.sub_zero] at hk
    have hs := (minFailInRange_go_eq_some isValid n 0 k).mp hk
    exact ⟨by omega, hs.2.2.1, fun j hj => hs.2.2.2 j (Nat.zero_le _) hj⟩

/-- GPU-side serialized `CGSNAP02` packet (`PersTier`, GPU constant table, declaration count, digest). -/
structure GpuArenaPacket where
  magic : Nat
  pers : SoATier
  gpuDecls : Array GpuConstDecl
  totalDecls : Nat
  closureHash : Nat
  deriving Repr, Inhabited

/-- Host-side `CGSNAP02` environment snapshot (`KEnv` plus closure digest). -/
structure HostEnvSnapshot where
  magic : Nat
  env : KEnv
  hostClosureHash : Nat
  deriving Repr, Inhabited

/-- `CGSNAP02` magic header identifier (`0x43475332`). -/
def cgsnap02Magic : Nat := 0x43475332

/-- Cryptographic closure-hash binding invariant between committed `(canonPers, canonEnv)` and
    serialized `(packet, host)` halves. -/
def DualSnapshotBinding (canonPers : SoATier) (canonEnv : KEnv)
    (packet : GpuArenaPacket) (host : HostEnvSnapshot) (expectedHash : Nat) : Prop :=
  (packet.magic = cgsnap02Magic -> packet.closureHash = expectedHash ->
    packet.pers = canonPers ∧
    packet.totalDecls = canonEnv.size ∧
    packet.gpuDecls.size = canonEnv.size ∧
    EnvSound packet.pers packet.gpuDecls canonEnv) ∧
  (host.magic = cgsnap02Magic -> host.hostClosureHash = expectedHash ->
    host.env = canonEnv)

/-- Outcome of restoring and running hybrid two-ended verification on a `CGSNAP02` dual snapshot. -/
structure DualRestoreResult where
  restored : Bool
  accepted : Bool
  minFailIdx : Option Nat
  deriving DecidableEq, Repr, Inhabited

/-- Validates `CGSNAP02` headers, sizes, and matching closure hashes, then executes hybrid
    two-ended work-stealing over `[0..totalDecls)` (rejecting immediately on any mismatch). -/
def restoreAndVerifyDual (packet : GpuArenaPacket) (host : HostEnvSnapshot)
    (expectedHash : Nat) (isValid : Nat -> Bool) (sched : List StealStep) :
    DualRestoreResult :=
  if packet.magic == cgsnap02Magic &&
     host.magic == cgsnap02Magic &&
     packet.closureHash == expectedHash &&
     host.hostClosureHash == expectedHash &&
     packet.totalDecls == host.env.size &&
     packet.gpuDecls.size == host.env.size
  then
    let fin := runHybridSteal isValid (HybridStealState.init packet.totalDecls) sched
    { restored := true
      accepted := fin.accepted
      minFailIdx := fin.combinedMinFail }
  else
    { restored := false, accepted := false, minFailIdx := none }

/-- **Theorem (`dualArenaSnapshot_sound`)**:
    Given a `CGSNAP02` dual `(GpuArenaPacket, HostEnvSnapshot)` committed to `(canonPers, canonEnv)`
    under `DualSnapshotBinding`, `restoreAndVerifyDual`:
    1. Rejects (`restored = false, accepted = false`) on any magic, size, or closure-hash mismatch.
    2. When restored with matching closure hash and drained schedule over `[0..canonEnv.size)`:
       binds `packet` and `host` to `(canonPers, canonEnv)` with `EnvSound packet.pers packet.gpuDecls canonEnv`,
       accepts iff every declaration `i < canonEnv.size` is kernel-valid (establishing `DeclVerified`
       and `HasType` across `[0..N)` when `isValid` is kernel-sound), and preserves the exact
       minimum failure index `minFailInRange isValid 0 canonEnv.size`. -/
theorem dualArenaSnapshot_sound
    {canonPers : SoATier} {canonEnv : KEnv}
    {packet : GpuArenaPacket} {host : HostEnvSnapshot} {expectedHash : Nat}
    {isValid : Nat -> Bool} {sched : List StealStep}
    (hbind : DualSnapshotBinding canonPers canonEnv packet host expectedHash)
    (hkernel : ∀ i d, canonEnv[i]? = some d -> isValid i = true -> DeclVerified canonEnv d)
    (hcomplete : ∀ i d, canonEnv[i]? = some d -> DeclVerified canonEnv d -> isValid i = true) :
    let res := restoreAndVerifyDual packet host expectedHash isValid sched
    (res.accepted = true -> res.restored = true) ∧
    (res.restored = true ->
      packet.pers = canonPers ∧
      host.env = canonEnv ∧
      EnvSound packet.pers packet.gpuDecls canonEnv ∧
      ((runHybridSteal isValid (HybridStealState.init packet.totalDecls) sched).gpuFront =
       (runHybridSteal isValid (HybridStealState.init packet.totalDecls) sched).cpuBack ->
        res.minFailIdx = minFailInRange isValid 0 canonEnv.size ∧
        (res.accepted = true ↔
          ∀ (i : Nat) (d : ConstDecl), canonEnv[i]? = some d ->
            DeclVerified canonEnv d ∧
            (∃ u, HasType canonEnv [] d.ty (.sort u))))) := by
  dsimp only
  unfold restoreAndVerifyDual
  cases hguard :
      (packet.magic == cgsnap02Magic &&
       host.magic == cgsnap02Magic &&
       packet.closureHash == expectedHash &&
       host.hostClosureHash == expectedHash &&
       packet.totalDecls == host.env.size &&
       packet.gpuDecls.size == host.env.size) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | true =>
    dsimp only
    simp only [Bool.and_eq_true, beq_iff_eq] at hguard
    rcases hguard with ⟨⟨⟨⟨⟨hpm, hhm⟩, hph⟩, hhh⟩, htd⟩, _⟩
    obtain ⟨hpers, hlen, _, henv⟩ := hbind.1 hpm hph
    have henvEq := hbind.2 hhm hhh
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    refine ⟨hpers, henvEq, henv, fun hdrained => ?_⟩
    have hsteal := twoEndedHybridSteal_sound isValid packet.totalDecls sched hdrained
    dsimp only at hsteal
    rw [hlen] at hsteal ⊢
    refine ⟨hsteal.1, ?_⟩
    constructor
    · intro hacc i d hlu
      have hi : i < canonEnv.size := by
        by_cases hlt : i < canonEnv.size
        · exact hlt
        · have hle : canonEnv.size ≤ i := Nat.le_of_not_lt hlt
          rw [Array.getElem?_eq_none hle] at hlu
          cases hlu
      have hvalid := hsteal.2.1.mp hacc i hi
      have hdv := hkernel i d hlu hvalid
      refine ⟨hdv, ?_⟩
      obtain ⟨f1, u, hty⟩ := hdv.1
      exact ⟨u, inferSpec_hasType canonEnv f1 [] d.ty (.sort u) hty⟩
    · intro hdecl
      apply hsteal.2.1.mpr
      intro i hi
      have hsome : canonEnv[i]? = some canonEnv[i] := Array.getElem?_eq_getElem hi
      exact hcomplete i canonEnv[i] hsome (hdecl i canonEnv[i] hsome).1

end ConGpuProof
