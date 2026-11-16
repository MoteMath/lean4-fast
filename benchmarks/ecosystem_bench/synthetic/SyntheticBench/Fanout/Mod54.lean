import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod54

open SyntheticBench

@[simp] def bias_54 (n : Nat) : Nat := n + 10

theorem mod54_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (55 : Int))).size = t.size := by simp
theorem mod54_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod54_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (56 : Int))).size = t.size := by simp
theorem mod54_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod54_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (57 : Int))).size = t.size := by simp
theorem mod54_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod54_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (58 : Int))).size = t.size := by simp
theorem mod54_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod54_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (59 : Int))).size = t.size := by simp
theorem mod54_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod54_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (60 : Int))).size = t.size := by simp
theorem mod54_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod54_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (61 : Int))).size = t.size := by simp
theorem mod54_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod54_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (62 : Int))).size = t.size := by simp
theorem mod54_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod54_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (63 : Int))).size = t.size := by simp
theorem mod54_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod54_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (64 : Int))).size = t.size := by simp
theorem mod54_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod54_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod54_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod54_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod54_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod54_tc_diamond (x y : Tagged 54 (Tagged 154 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod54_bignat256 : (90030001994139385094940323956944596855057070885091015141488027091856224225451 : Nat) + 59780829226594561805076840285776839777099183128532547880029543990330623052667 = 149810831220733946900017164242721436632156254013623563021517571082186847278118 := rfl
theorem mod54_arith (x y : Nat) (h : x + 54 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod54
