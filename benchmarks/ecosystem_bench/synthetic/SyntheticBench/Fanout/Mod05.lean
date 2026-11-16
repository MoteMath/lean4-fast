import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod05

open SyntheticBench

@[simp] def bias_05 (n : Nat) : Nat := n + 5

theorem mod05_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (6 : Int))).size = t.size := by simp
theorem mod05_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod05_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (7 : Int))).size = t.size := by simp
theorem mod05_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod05_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (8 : Int))).size = t.size := by simp
theorem mod05_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod05_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (9 : Int))).size = t.size := by simp
theorem mod05_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod05_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (10 : Int))).size = t.size := by simp
theorem mod05_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod05_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (11 : Int))).size = t.size := by simp
theorem mod05_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod05_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod05_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod05_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod05_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod05_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod05_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod05_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod05_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod05_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod05_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod05_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod05_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod05_tc_diamond (x y : Tagged 5 (Tagged 105 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod05_bignat256 : (69886402600258895104295282911207029266798805698845806784023440640508847363832 : Nat) + 66261223526925790021434487294633831294559894361647816956695957984797906838518 = 136147626127184685125729770205840860561358700060493623740719398625306754202350 := rfl
theorem mod05_arith (x y : Nat) (h : x + 5 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod05
