import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod18

open SyntheticBench

@[simp] def bias_18 (n : Nat) : Nat := n + 7

theorem mod18_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (19 : Int))).size = t.size := by simp
theorem mod18_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod18_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (20 : Int))).size = t.size := by simp
theorem mod18_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod18_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (21 : Int))).size = t.size := by simp
theorem mod18_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod18_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (22 : Int))).size = t.size := by simp
theorem mod18_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod18_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (23 : Int))).size = t.size := by simp
theorem mod18_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod18_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (24 : Int))).size = t.size := by simp
theorem mod18_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod18_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (25 : Int))).size = t.size := by simp
theorem mod18_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod18_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (26 : Int))).size = t.size := by simp
theorem mod18_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod18_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (27 : Int))).size = t.size := by simp
theorem mod18_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod18_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (28 : Int))).size = t.size := by simp
theorem mod18_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod18_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (29 : Int))).size = t.size := by simp
theorem mod18_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod18_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (30 : Int))).size = t.size := by simp
theorem mod18_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod18_tc_diamond (x y : Tagged 18 (Tagged 118 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod18_bignat256 : (91772349881517257100330381242698532308472204814729863863926398823543221270463 : Nat) + 69268142967136533367155630822622294856372537816567947632409163149721968011911 = 161040492848653790467486012065320827164844742631297811496335561973265189282374 := rfl
theorem mod18_arith (x y : Nat) (h : x + 18 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod18
