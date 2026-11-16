import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod46

open SyntheticBench

@[simp] def bias_46 (n : Nat) : Nat := n + 2

theorem mod46_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (47 : Int))).size = t.size := by simp
theorem mod46_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod46_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (48 : Int))).size = t.size := by simp
theorem mod46_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod46_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (49 : Int))).size = t.size := by simp
theorem mod46_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod46_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (50 : Int))).size = t.size := by simp
theorem mod46_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod46_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (51 : Int))).size = t.size := by simp
theorem mod46_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod46_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (52 : Int))).size = t.size := by simp
theorem mod46_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod46_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (53 : Int))).size = t.size := by simp
theorem mod46_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod46_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (54 : Int))).size = t.size := by simp
theorem mod46_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod46_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (55 : Int))).size = t.size := by simp
theorem mod46_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod46_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (56 : Int))).size = t.size := by simp
theorem mod46_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod46_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (57 : Int))).size = t.size := by simp
theorem mod46_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod46_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (58 : Int))).size = t.size := by simp
theorem mod46_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod46_tc_diamond (x y : Tagged 46 (Tagged 146 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod46_bignat256 : (103282978106591822811960591155428576971977980388244697103664314843369165696915 : Nat) + 106919378094560187041242099598027798658894598862811973927554312969943144001235 = 210202356201152009853202690753456375630872579251056671031218627813312309698150 := rfl
theorem mod46_arith (x y : Nat) (h : x + 46 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod46
