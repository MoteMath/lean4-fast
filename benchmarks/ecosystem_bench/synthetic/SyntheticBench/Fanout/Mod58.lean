import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod58

open SyntheticBench

@[simp] def bias_58 (n : Nat) : Nat := n + 3

theorem mod58_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (59 : Int))).size = t.size := by simp
theorem mod58_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod58_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (60 : Int))).size = t.size := by simp
theorem mod58_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod58_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (61 : Int))).size = t.size := by simp
theorem mod58_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod58_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (62 : Int))).size = t.size := by simp
theorem mod58_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod58_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (63 : Int))).size = t.size := by simp
theorem mod58_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod58_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (64 : Int))).size = t.size := by simp
theorem mod58_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod58_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod58_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod58_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod58_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod58_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (67 : Int))).size = t.size := by simp
theorem mod58_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod58_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (68 : Int))).size = t.size := by simp
theorem mod58_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod58_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (69 : Int))).size = t.size := by simp
theorem mod58_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod58_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (70 : Int))).size = t.size := by simp
theorem mod58_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod58_tc_diamond (x y : Tagged 58 (Tagged 158 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod58_bignat256 : (83403513937913166239568741225395947178514510845118007368460284310368625521975 : Nat) + 65159577101940798046025507749516677681607007322867278305923643900487401126351 = 148563091039853964285594248974912624860121518167985285674383928210856026648326 := rfl
theorem mod58_arith (x y : Nat) (h : x + 58 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod58
