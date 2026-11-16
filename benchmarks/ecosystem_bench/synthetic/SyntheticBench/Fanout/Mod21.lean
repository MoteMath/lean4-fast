import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod21

open SyntheticBench

@[simp] def bias_21 (n : Nat) : Nat := n + 10

theorem mod21_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (22 : Int))).size = t.size := by simp
theorem mod21_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod21_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (23 : Int))).size = t.size := by simp
theorem mod21_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod21_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (24 : Int))).size = t.size := by simp
theorem mod21_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod21_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (25 : Int))).size = t.size := by simp
theorem mod21_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod21_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (26 : Int))).size = t.size := by simp
theorem mod21_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod21_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (27 : Int))).size = t.size := by simp
theorem mod21_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod21_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (28 : Int))).size = t.size := by simp
theorem mod21_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod21_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (29 : Int))).size = t.size := by simp
theorem mod21_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod21_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (30 : Int))).size = t.size := by simp
theorem mod21_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod21_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (31 : Int))).size = t.size := by simp
theorem mod21_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod21_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (32 : Int))).size = t.size := by simp
theorem mod21_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod21_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (33 : Int))).size = t.size := by simp
theorem mod21_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod21_tc_diamond (x y : Tagged 21 (Tagged 121 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod21_bignat256 : (101276494994012117388317342753969703723768050815487329758965387193335331965224 : Nat) + 87776215028310734978952055414206502148074836981937195317206359477950029094214 = 189052710022322852367269398168176205871842887797424525076171746671285361059438 := rfl
theorem mod21_arith (x y : Nat) (h : x + 21 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod21
