import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod64

open SyntheticBench

@[simp] def bias_64 (n : Nat) : Nat := n + 9

theorem mod64_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod64_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod64_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod64_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod64_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (67 : Int))).size = t.size := by simp
theorem mod64_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod64_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (68 : Int))).size = t.size := by simp
theorem mod64_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod64_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (69 : Int))).size = t.size := by simp
theorem mod64_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod64_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (70 : Int))).size = t.size := by simp
theorem mod64_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod64_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (71 : Int))).size = t.size := by simp
theorem mod64_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod64_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (72 : Int))).size = t.size := by simp
theorem mod64_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod64_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (73 : Int))).size = t.size := by simp
theorem mod64_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod64_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (74 : Int))).size = t.size := by simp
theorem mod64_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod64_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (75 : Int))).size = t.size := by simp
theorem mod64_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod64_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (76 : Int))).size = t.size := by simp
theorem mod64_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod64_tc_diamond (x y : Tagged 64 (Tagged 164 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod64_bignat256 : (102411804162902886802988460777164928481434624000217606326351996905098487437321 : Nat) + 102175721224289201257064153461911730737340026807190440843313325668015454265165 = 204587525387192088060052614239076659218774650807408047169665322573113941702486 := rfl
theorem mod64_arith (x y : Nat) (h : x + 64 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod64
