import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod15

open SyntheticBench

@[simp] def bias_15 (n : Nat) : Nat := n + 4

theorem mod15_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (16 : Int))).size = t.size := by simp
theorem mod15_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod15_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (17 : Int))).size = t.size := by simp
theorem mod15_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod15_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (18 : Int))).size = t.size := by simp
theorem mod15_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod15_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (19 : Int))).size = t.size := by simp
theorem mod15_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod15_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (20 : Int))).size = t.size := by simp
theorem mod15_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod15_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (21 : Int))).size = t.size := by simp
theorem mod15_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod15_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (22 : Int))).size = t.size := by simp
theorem mod15_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod15_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (23 : Int))).size = t.size := by simp
theorem mod15_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod15_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (24 : Int))).size = t.size := by simp
theorem mod15_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod15_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (25 : Int))).size = t.size := by simp
theorem mod15_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod15_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (26 : Int))).size = t.size := by simp
theorem mod15_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod15_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (27 : Int))).size = t.size := by simp
theorem mod15_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod15_tc_diamond (x y : Tagged 15 (Tagged 115 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod15_bignat256 : (82268204769022396818620521466814041657012148237180064384971319154141435536982 : Nat) + 108656115524620429473421800470768722254800738040305709919979739662482738051016 = 190924320293642826292042321937582763911812886277485774304951058816624173587998 := rfl
theorem mod15_arith (x y : Nat) (h : x + 15 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod15
