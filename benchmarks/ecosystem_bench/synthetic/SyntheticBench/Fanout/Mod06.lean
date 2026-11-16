import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod06

open SyntheticBench

@[simp] def bias_06 (n : Nat) : Nat := n + 6

theorem mod06_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (7 : Int))).size = t.size := by simp
theorem mod06_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod06_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (8 : Int))).size = t.size := by simp
theorem mod06_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod06_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (9 : Int))).size = t.size := by simp
theorem mod06_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod06_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (10 : Int))).size = t.size := by simp
theorem mod06_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod06_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (11 : Int))).size = t.size := by simp
theorem mod06_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod06_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (12 : Int))).size = t.size := by simp
theorem mod06_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod06_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (13 : Int))).size = t.size := by simp
theorem mod06_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod06_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (14 : Int))).size = t.size := by simp
theorem mod06_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod06_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (15 : Int))).size = t.size := by simp
theorem mod06_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod06_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod06_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod06_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod06_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod06_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (18 : Int))).size = t.size := by simp
theorem mod06_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod06_tc_diamond (x y : Tagged 6 (Tagged 106 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod06_bignat256 : (111651814050195913672722231172731162101935674357856553599130429356543761445403 : Nat) + 111027943959755922362372222671133415833660129356512643254039832219177710886795 = 222679758009951836035094453843864577935595803714369196853170261575721472332198 := rfl
theorem mod06_arith (x y : Nat) (h : x + 6 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod06
