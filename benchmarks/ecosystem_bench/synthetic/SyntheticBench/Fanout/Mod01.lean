import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod01

open SyntheticBench

@[simp] def bias_01 (n : Nat) : Nat := n + 1

theorem mod01_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (2 : Int))).size = t.size := by simp
theorem mod01_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod01_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (3 : Int))).size = t.size := by simp
theorem mod01_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod01_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (4 : Int))).size = t.size := by simp
theorem mod01_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod01_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (5 : Int))).size = t.size := by simp
theorem mod01_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod01_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (6 : Int))).size = t.size := by simp
theorem mod01_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod01_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (7 : Int))).size = t.size := by simp
theorem mod01_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod01_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (8 : Int))).size = t.size := by simp
theorem mod01_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod01_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (9 : Int))).size = t.size := by simp
theorem mod01_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod01_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (10 : Int))).size = t.size := by simp
theorem mod01_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod01_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (11 : Int))).size = t.size := by simp
theorem mod01_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod01_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod01_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod01_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod01_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod01_tc_diamond (x y : Tagged 1 (Tagged 101 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod01_bignat256 : (76512890656485113959666865642755678943341365738818814557051183421996446067308 : Nat) + 60882475651579553780485819830893993390392352534234024994265232682072896976290 = 137395366308064667740152685473649672333733718273052839551316416104069343043598 := rfl
theorem mod01_arith (x y : Nat) (h : x + 1 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod01
