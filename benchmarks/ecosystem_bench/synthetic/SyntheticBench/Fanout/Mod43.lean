import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod43

open SyntheticBench

@[simp] def bias_43 (n : Nat) : Nat := n + 10

theorem mod43_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (44 : Int))).size = t.size := by simp
theorem mod43_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod43_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (45 : Int))).size = t.size := by simp
theorem mod43_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod43_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (46 : Int))).size = t.size := by simp
theorem mod43_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod43_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (47 : Int))).size = t.size := by simp
theorem mod43_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod43_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (48 : Int))).size = t.size := by simp
theorem mod43_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod43_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (49 : Int))).size = t.size := by simp
theorem mod43_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod43_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (50 : Int))).size = t.size := by simp
theorem mod43_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod43_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (51 : Int))).size = t.size := by simp
theorem mod43_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod43_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (52 : Int))).size = t.size := by simp
theorem mod43_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod43_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (53 : Int))).size = t.size := by simp
theorem mod43_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod43_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (54 : Int))).size = t.size := by simp
theorem mod43_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod43_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (55 : Int))).size = t.size := by simp
theorem mod43_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod43_tc_diamond (x y : Tagged 43 (Tagged 143 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod43_bignat256 : (93778832994096962523973629644157405556682134387487231208625326473577055002154 : Nat) + 88411306033385985435722776741830272131028089120650392658859472086179117431828 = 182190139027482947959696406385987677687710223508137623867484798559756172433982 := rfl
theorem mod43_arith (x y : Nat) (h : x + 43 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod43
