import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod30

open SyntheticBench

@[simp] def bias_30 (n : Nat) : Nat := n + 8

theorem mod30_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (31 : Int))).size = t.size := by simp
theorem mod30_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod30_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (32 : Int))).size = t.size := by simp
theorem mod30_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod30_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (33 : Int))).size = t.size := by simp
theorem mod30_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod30_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (34 : Int))).size = t.size := by simp
theorem mod30_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod30_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (35 : Int))).size = t.size := by simp
theorem mod30_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod30_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (36 : Int))).size = t.size := by simp
theorem mod30_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod30_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (37 : Int))).size = t.size := by simp
theorem mod30_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod30_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (38 : Int))).size = t.size := by simp
theorem mod30_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod30_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (39 : Int))).size = t.size := by simp
theorem mod30_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod30_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (40 : Int))).size = t.size := by simp
theorem mod30_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod30_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (41 : Int))).size = t.size := by simp
theorem mod30_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod30_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (42 : Int))).size = t.size := by simp
theorem mod30_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod30_tc_diamond (x y : Tagged 30 (Tagged 130 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod30_bignat256 : (71892885712838600527938531312665902515008735271603174128722368290542681095523 : Nat) + 85404386593175242083724531478455127805379656242522595567043911476791021745539 = 157297272306013842611663062791121030320388391514125769695766279767333702841062 := rfl
theorem mod30_arith (x y : Nat) (h : x + 30 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod30
