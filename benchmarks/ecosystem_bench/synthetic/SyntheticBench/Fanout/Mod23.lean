import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod23

open SyntheticBench

@[simp] def bias_23 (n : Nat) : Nat := n + 1

theorem mod23_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (24 : Int))).size = t.size := by simp
theorem mod23_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod23_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (25 : Int))).size = t.size := by simp
theorem mod23_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod23_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (26 : Int))).size = t.size := by simp
theorem mod23_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod23_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (27 : Int))).size = t.size := by simp
theorem mod23_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod23_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (28 : Int))).size = t.size := by simp
theorem mod23_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod23_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (29 : Int))).size = t.size := by simp
theorem mod23_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod23_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (30 : Int))).size = t.size := by simp
theorem mod23_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod23_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (31 : Int))).size = t.size := by simp
theorem mod23_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod23_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (32 : Int))).size = t.size := by simp
theorem mod23_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod23_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (33 : Int))).size = t.size := by simp
theorem mod23_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod23_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (34 : Int))).size = t.size := by simp
theorem mod23_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod23_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (35 : Int))).size = t.size := by simp
theorem mod23_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod23_tc_diamond (x y : Tagged 23 (Tagged 123 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod23_bignat256 : (69015228656569959101600254268330061540091238734026382422813478146702203617134 : Nat) + 61517566656654804237256541158517763373005322306026283872454970682870217102448 = 130532795313224763338856795426847824913096561040052666295268448829572420719582 := rfl
theorem mod23_arith (x y : Nat) (h : x + 23 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod23
