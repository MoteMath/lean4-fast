import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod11

open SyntheticBench

@[simp] def bias_11 (n : Nat) : Nat := n + 0

theorem mod11_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod11_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod11_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod11_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod11_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod11_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod11_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod11_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod11_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod11_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod11_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod11_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod11_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (18 : Int))).size = t.size := by simp
theorem mod11_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod11_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (19 : Int))).size = t.size := by simp
theorem mod11_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod11_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (20 : Int))).size = t.size := by simp
theorem mod11_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod11_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (21 : Int))).size = t.size := by simp
theorem mod11_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod11_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (22 : Int))).size = t.size := by simp
theorem mod11_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod11_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (23 : Int))).size = t.size := by simp
theorem mod11_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod11_tc_diamond (x y : Tagged 11 (Tagged 111 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod11_bignat256 : (88894692825248615673992104198362691333554708277153072158017508679702743792074 : Nat) + 103277367649274193232473133007028884350633196212891917957549014359757728188788 = 192172060474522808906465237205391575684187904490044990115566523039460471980862 := rfl
theorem mod11_arith (x y : Nat) (h : x + 11 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod11
