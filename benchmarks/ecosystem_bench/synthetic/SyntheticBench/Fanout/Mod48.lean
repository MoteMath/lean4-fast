import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod48

open SyntheticBench

@[simp] def bias_48 (n : Nat) : Nat := n + 4

theorem mod48_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (49 : Int))).size = t.size := by simp
theorem mod48_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod48_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (50 : Int))).size = t.size := by simp
theorem mod48_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod48_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (51 : Int))).size = t.size := by simp
theorem mod48_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod48_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (52 : Int))).size = t.size := by simp
theorem mod48_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod48_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (53 : Int))).size = t.size := by simp
theorem mod48_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod48_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (54 : Int))).size = t.size := by simp
theorem mod48_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod48_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (55 : Int))).size = t.size := by simp
theorem mod48_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod48_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (56 : Int))).size = t.size := by simp
theorem mod48_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod48_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (57 : Int))).size = t.size := by simp
theorem mod48_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod48_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (58 : Int))).size = t.size := by simp
theorem mod48_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod48_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (59 : Int))).size = t.size := by simp
theorem mod48_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod48_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (60 : Int))).size = t.size := by simp
theorem mod48_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod48_tc_diamond (x y : Tagged 48 (Tagged 148 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod48_bignat256 : (71021711769149664525243502669788934788301168306783749767493959052662327797209 : Nat) + 80660729722904256305823687077725740647660873610108728898905279619327366522365 = 151682441492053920831067189747514675435962041916892478666399238671989694319574 := rfl
theorem mod48_arith (x y : Nat) (h : x + 48 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod48
