import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod60

open SyntheticBench

@[simp] def bias_60 (n : Nat) : Nat := n + 5

theorem mod60_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (61 : Int))).size = t.size := by simp
theorem mod60_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod60_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (62 : Int))).size = t.size := by simp
theorem mod60_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod60_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (63 : Int))).size = t.size := by simp
theorem mod60_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod60_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (64 : Int))).size = t.size := by simp
theorem mod60_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod60_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod60_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod60_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod60_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod60_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (67 : Int))).size = t.size := by simp
theorem mod60_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod60_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (68 : Int))).size = t.size := by simp
theorem mod60_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod60_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (69 : Int))).size = t.size := by simp
theorem mod60_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod60_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (70 : Int))).size = t.size := by simp
theorem mod60_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod60_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (71 : Int))).size = t.size := by simp
theorem mod60_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod60_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (72 : Int))).size = t.size := by simp
theorem mod60_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod60_tc_diamond (x y : Tagged 60 (Tagged 160 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod60_bignat256 : (109038292219129105664637145244100258921812973463398280515482095131050120653693 : Nat) + 96796973348942965022392587733558573597008274402984315297003402553828188467449 = 205835265568072070687029732977658832518821247866382595812485497684878309121142 := rfl
theorem mod60_arith (x y : Nat) (h : x + 60 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod60
