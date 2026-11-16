import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod13

open SyntheticBench

@[simp] def bias_13 (n : Nat) : Nat := n + 2

theorem mod13_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod13_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod13_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod13_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod13_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod13_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod13_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod13_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod13_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (18 : Int))).size = t.size := by simp
theorem mod13_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod13_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (19 : Int))).size = t.size := by simp
theorem mod13_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod13_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (20 : Int))).size = t.size := by simp
theorem mod13_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod13_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (21 : Int))).size = t.size := by simp
theorem mod13_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod13_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (22 : Int))).size = t.size := by simp
theorem mod13_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod13_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (23 : Int))).size = t.size := by simp
theorem mod13_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod13_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (24 : Int))).size = t.size := by simp
theorem mod13_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod13_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (25 : Int))).size = t.size := by simp
theorem mod13_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod13_tc_diamond (x y : Tagged 13 (Tagged 113 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod13_bignat256 : (114529471106464555099060508217067003076512888528512406841575944892952470712336 : Nat) + 77018719277618262497054720486726826339399470960188672928899981009141950709918 = 191548190384082817596115228703793829415912359488701079770475925902094421422254 := rfl
theorem mod13_arith (x y : Nat) (h : x + 13 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod13
