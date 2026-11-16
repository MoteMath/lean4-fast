import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod14

open SyntheticBench

@[simp] def bias_14 (n : Nat) : Nat := n + 3

theorem mod14_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod14_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod14_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod14_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod14_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod14_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod14_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (18 : Int))).size = t.size := by simp
theorem mod14_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod14_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (19 : Int))).size = t.size := by simp
theorem mod14_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod14_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (20 : Int))).size = t.size := by simp
theorem mod14_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod14_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (21 : Int))).size = t.size := by simp
theorem mod14_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod14_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (22 : Int))).size = t.size := by simp
theorem mod14_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod14_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (23 : Int))).size = t.size := by simp
theorem mod14_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod14_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (24 : Int))).size = t.size := by simp
theorem mod14_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod14_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (25 : Int))).size = t.size := by simp
theorem mod14_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod14_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (26 : Int))).size = t.size := by simp
theorem mod14_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod14_tc_diamond (x y : Tagged 14 (Tagged 114 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod14_bignat256 : (98398837937743475961979065709633862748850554277910538053056497049494854486835 : Nat) + 63889395091790297132484065094269137715700503045440883622617418684029224451123 = 162288233029533773094463130803903000464551057323351421675673915733524078937958 := rfl
theorem mod14_arith (x y : Nat) (h : x + 14 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod14
