import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod49

open SyntheticBench

@[simp] def bias_49 (n : Nat) : Nat := n + 5

theorem mod49_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (50 : Int))).size = t.size := by simp
theorem mod49_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod49_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (51 : Int))).size = t.size := by simp
theorem mod49_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod49_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (52 : Int))).size = t.size := by simp
theorem mod49_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod49_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (53 : Int))).size = t.size := by simp
theorem mod49_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod49_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (54 : Int))).size = t.size := by simp
theorem mod49_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod49_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (55 : Int))).size = t.size := by simp
theorem mod49_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod49_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (56 : Int))).size = t.size := by simp
theorem mod49_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod49_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (57 : Int))).size = t.size := by simp
theorem mod49_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod49_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (58 : Int))).size = t.size := by simp
theorem mod49_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod49_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (59 : Int))).size = t.size := by simp
theorem mod49_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod49_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (60 : Int))).size = t.size := by simp
theorem mod49_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod49_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (61 : Int))).size = t.size := by simp
theorem mod49_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod49_tc_diamond (x y : Tagged 49 (Tagged 149 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod49_bignat256 : (112787123219086683093670450931313067623097754598873558119137573161265473667324 : Nat) + 67531405537076290934975929949881371260126116272153273176520361849750605750674 = 180318528756162974028646380881194438883223870871026831295657935011016079417998 := rfl
theorem mod49_arith (x y : Nat) (h : x + 49 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod49
