import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod07

open SyntheticBench

@[simp] def bias_07 (n : Nat) : Nat := n + 7

theorem mod07_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (8 : Int))).size = t.size := by simp
theorem mod07_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod07_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (9 : Int))).size = t.size := by simp
theorem mod07_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod07_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (10 : Int))).size = t.size := by simp
theorem mod07_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod07_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (11 : Int))).size = t.size := by simp
theorem mod07_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod07_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod07_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod07_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod07_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod07_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod07_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod07_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod07_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod07_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod07_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod07_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod07_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod07_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (18 : Int))).size = t.size := by simp
theorem mod07_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod07_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (19 : Int))).size = t.size := by simp
theorem mod07_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod07_tc_diamond (x y : Tagged 7 (Tagged 107 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod07_bignat256 : (95521180881474834529363686929911341010097268317126079931045251461190342495550 : Nat) + 97898619773927956997801567278675727209961161441764853947757269894064984628000 = 193419800655402791527165254208587068220058429758890933878802521355255327123550 := rfl
theorem mod07_arith (x y : Nat) (h : x + 7 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod07
