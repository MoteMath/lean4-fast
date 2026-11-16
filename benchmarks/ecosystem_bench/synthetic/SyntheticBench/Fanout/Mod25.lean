import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod25

open SyntheticBench

@[simp] def bias_25 (n : Nat) : Nat := n + 3

theorem mod25_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (26 : Int))).size = t.size := by simp
theorem mod25_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod25_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (27 : Int))).size = t.size := by simp
theorem mod25_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod25_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (28 : Int))).size = t.size := by simp
theorem mod25_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod25_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (29 : Int))).size = t.size := by simp
theorem mod25_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod25_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (30 : Int))).size = t.size := by simp
theorem mod25_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod25_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (31 : Int))).size = t.size := by simp
theorem mod25_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod25_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (32 : Int))).size = t.size := by simp
theorem mod25_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod25_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (33 : Int))).size = t.size := by simp
theorem mod25_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod25_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (34 : Int))).size = t.size := by simp
theorem mod25_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod25_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (35 : Int))).size = t.size := by simp
theorem mod25_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod25_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (36 : Int))).size = t.size := by simp
theorem mod25_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod25_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (37 : Int))).size = t.size := by simp
theorem mod25_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod25_tc_diamond (x y : Tagged 25 (Tagged 125 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod25_bignat256 : (94650006937785898526668658287034373283389701352306655569835288967383698748852 : Nat) + 93154962903656971213623621142559659288746871753064259326998103943642772655002 = 187804969841442869740292279429594032572136573105370914896833392911026471403854 := rfl
theorem mod25_arith (x y : Nat) (h : x + 25 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod25
