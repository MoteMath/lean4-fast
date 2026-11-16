import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod08

open SyntheticBench

@[simp] def bias_08 (n : Nat) : Nat := n + 8

theorem mod08_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (9 : Int))).size = t.size := by simp
theorem mod08_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod08_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (10 : Int))).size = t.size := by simp
theorem mod08_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod08_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (11 : Int))).size = t.size := by simp
theorem mod08_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod08_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod08_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod08_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod08_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod08_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod08_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod08_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod08_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod08_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod08_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod08_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod08_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod08_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (18 : Int))).size = t.size := by simp
theorem mod08_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod08_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (19 : Int))).size = t.size := by simp
theorem mod08_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod08_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (20 : Int))).size = t.size := by simp
theorem mod08_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod08_tc_diamond (x y : Tagged 8 (Tagged 108 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod08_bignat256 : (79390547712753755392282244422478200682094651699603272679062429010300958058593 : Nat) + 84769295588099991626953810150831357822766686470730336688854173475993701619381 = 164159843300853747019236054573309558504861338170333609367916602486294659677974 := rfl
theorem mod08_arith (x y : Nat) (h : x + 8 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod08
