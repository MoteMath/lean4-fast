import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod02

open SyntheticBench

@[simp] def bias_02 (n : Nat) : Nat := n + 2

theorem mod02_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (3 : Int))).size = t.size := by simp
theorem mod02_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod02_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (4 : Int))).size = t.size := by simp
theorem mod02_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod02_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (5 : Int))).size = t.size := by simp
theorem mod02_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod02_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (6 : Int))).size = t.size := by simp
theorem mod02_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod02_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (7 : Int))).size = t.size := by simp
theorem mod02_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod02_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (8 : Int))).size = t.size := by simp
theorem mod02_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod02_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (9 : Int))).size = t.size := by simp
theorem mod02_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod02_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (10 : Int))).size = t.size := by simp
theorem mod02_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod02_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (11 : Int))).size = t.size := by simp
theorem mod02_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod02_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod02_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod02_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod02_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod02_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod02_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod02_tc_diamond (x y : Tagged 2 (Tagged 102 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod02_bignat256 : (60382257487764034822585423135322538615338749121296007305068360971107061630351 : Nat) + 105649196084409686127700656942780258693328376952306517707711462360916735537463 = 166031453572173720950286080078102797308667126073602525012779823332023797167814 := rfl
theorem mod02_arith (x y : Nat) (h : x + 2 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod02
