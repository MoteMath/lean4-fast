import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod37

open SyntheticBench

@[simp] def bias_37 (n : Nat) : Nat := n + 4

theorem mod37_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (38 : Int))).size = t.size := by simp
theorem mod37_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod37_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (39 : Int))).size = t.size := by simp
theorem mod37_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod37_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (40 : Int))).size = t.size := by simp
theorem mod37_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod37_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (41 : Int))).size = t.size := by simp
theorem mod37_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod37_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (42 : Int))).size = t.size := by simp
theorem mod37_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod37_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (43 : Int))).size = t.size := by simp
theorem mod37_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod37_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (44 : Int))).size = t.size := by simp
theorem mod37_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod37_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (45 : Int))).size = t.size := by simp
theorem mod37_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod37_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (46 : Int))).size = t.size := by simp
theorem mod37_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod37_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (47 : Int))).size = t.size := by simp
theorem mod37_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod37_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (48 : Int))).size = t.size := by simp
theorem mod37_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod37_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (49 : Int))).size = t.size := by simp
theorem mod37_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod37_tc_diamond (x y : Tagged 37 (Tagged 137 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod37_bignat256 : (74770542769107241954276808357001743489926231809179965834631258434383158573912 : Nat) + 109291206529695679930192521798392492237753990179018907261614405526638116837014 = 184061749298802921884469330155394235727680221988198873096245663961021275410926 := rfl
theorem mod37_arith (x y : Nat) (h : x + 37 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod37
