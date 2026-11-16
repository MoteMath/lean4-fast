import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod42

open SyntheticBench

@[simp] def bias_42 (n : Nat) : Nat := n + 9

theorem mod42_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (43 : Int))).size = t.size := by simp
theorem mod42_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod42_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (44 : Int))).size = t.size := by simp
theorem mod42_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod42_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (45 : Int))).size = t.size := by simp
theorem mod42_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod42_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (46 : Int))).size = t.size := by simp
theorem mod42_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod42_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (47 : Int))).size = t.size := by simp
theorem mod42_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod42_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (48 : Int))).size = t.size := by simp
theorem mod42_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod42_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (49 : Int))).size = t.size := by simp
theorem mod42_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod42_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (50 : Int))).size = t.size := by simp
theorem mod42_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod42_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (51 : Int))).size = t.size := by simp
theorem mod42_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod42_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (52 : Int))).size = t.size := by simp
theorem mod42_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod42_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (53 : Int))).size = t.size := by simp
theorem mod42_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod42_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (54 : Int))).size = t.size := by simp
theorem mod42_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod42_tc_diamond (x y : Tagged 42 (Tagged 142 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod42_bignat256 : (109909466162818041667332173886977226648520540428217704876692057624856764400391 : Nat) + 101540630219213950800293432134287960754727057035398181965123587667218134139007 = 211450096382031992467625606021265187403247597463615886841815645292074898539398 := rfl
theorem mod42_arith (x y : Nat) (h : x + 42 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod42
