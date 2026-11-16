import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod31

open SyntheticBench

@[simp] def bias_31 (n : Nat) : Nat := n + 9

theorem mod31_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (32 : Int))).size = t.size := by simp
theorem mod31_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod31_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (33 : Int))).size = t.size := by simp
theorem mod31_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod31_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (34 : Int))).size = t.size := by simp
theorem mod31_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod31_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (35 : Int))).size = t.size := by simp
theorem mod31_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod31_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (36 : Int))).size = t.size := by simp
theorem mod31_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod31_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (37 : Int))).size = t.size := by simp
theorem mod31_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod31_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (38 : Int))).size = t.size := by simp
theorem mod31_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod31_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (39 : Int))).size = t.size := by simp
theorem mod31_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod31_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (40 : Int))).size = t.size := by simp
theorem mod31_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod31_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (41 : Int))).size = t.size := by simp
theorem mod31_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod31_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (42 : Int))).size = t.size := by simp
theorem mod31_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod31_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (43 : Int))).size = t.size := by simp
theorem mod31_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod31_tc_diamond (x y : Tagged 31 (Tagged 131 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod31_bignat256 : (113658297162775619096365479574190035349805321563692982480365982399145826965638 : Nat) + 72275062407347276719153876085997439181680688327774806260761349151678295486744 = 185933359570122895815519355660187474531486009891467788741127331550824122452382 := rfl
theorem mod31_arith (x y : Nat) (h : x + 31 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod31
