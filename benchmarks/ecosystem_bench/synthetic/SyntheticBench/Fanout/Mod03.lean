import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod03

open SyntheticBench

@[simp] def bias_03 (n : Nat) : Nat := n + 3

theorem mod03_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (4 : Int))).size = t.size := by simp
theorem mod03_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod03_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (5 : Int))).size = t.size := by simp
theorem mod03_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod03_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (6 : Int))).size = t.size := by simp
theorem mod03_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod03_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (7 : Int))).size = t.size := by simp
theorem mod03_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod03_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (8 : Int))).size = t.size := by simp
theorem mod03_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod03_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (9 : Int))).size = t.size := by simp
theorem mod03_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod03_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (10 : Int))).size = t.size := by simp
theorem mod03_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod03_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (11 : Int))).size = t.size := by simp
theorem mod03_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod03_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod03_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod03_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod03_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod03_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod03_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod03_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod03_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod03_tc_diamond (x y : Tagged 3 (Tagged 103 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod03_bignat256 : (102147668937701053391012371396846671450475617780306754120175349687141975711922 : Nat) + 92519871898581720756852899814935889305793619614351061985344991335413684317388 = 194667540836282774147865271211782560756269237394657816105520341022555660029310 := rfl
theorem mod03_arith (x y : Nat) (h : x + 3 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod03
