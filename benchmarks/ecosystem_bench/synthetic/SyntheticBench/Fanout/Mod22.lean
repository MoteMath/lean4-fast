import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod22

open SyntheticBench

@[simp] def bias_22 (n : Nat) : Nat := n + 0

theorem mod22_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (23 : Int))).size = t.size := by simp
theorem mod22_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod22_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (24 : Int))).size = t.size := by simp
theorem mod22_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod22_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (25 : Int))).size = t.size := by simp
theorem mod22_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod22_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (26 : Int))).size = t.size := by simp
theorem mod22_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod22_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (27 : Int))).size = t.size := by simp
theorem mod22_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod22_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (28 : Int))).size = t.size := by simp
theorem mod22_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod22_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (29 : Int))).size = t.size := by simp
theorem mod22_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod22_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (30 : Int))).size = t.size := by simp
theorem mod22_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod22_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (31 : Int))).size = t.size := by simp
theorem mod22_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod22_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (32 : Int))).size = t.size := by simp
theorem mod22_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod22_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (33 : Int))).size = t.size := by simp
theorem mod22_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod22_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (34 : Int))).size = t.size := by simp
theorem mod22_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod22_tc_diamond (x y : Tagged 22 (Tagged 122 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod22_bignat256 : (85145861825291038244958798511149882631929644774756856090880209297981913015371 : Nat) + 74646890842482769608104298286362132760540079643981739594821441708373268322523 = 159792752667773807853063096797512015392469724418738595685701651006355181337894 := rfl
theorem mod22_arith (x y : Nat) (h : x + 22 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod22
