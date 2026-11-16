import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod36

open SyntheticBench

@[simp] def bias_36 (n : Nat) : Nat := n + 3

theorem mod36_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (37 : Int))).size = t.size := by simp
theorem mod36_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod36_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (38 : Int))).size = t.size := by simp
theorem mod36_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod36_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (39 : Int))).size = t.size := by simp
theorem mod36_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod36_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (40 : Int))).size = t.size := by simp
theorem mod36_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod36_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (41 : Int))).size = t.size := by simp
theorem mod36_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod36_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (42 : Int))).size = t.size := by simp
theorem mod36_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod36_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (43 : Int))).size = t.size := by simp
theorem mod36_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod36_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (44 : Int))).size = t.size := by simp
theorem mod36_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod36_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (45 : Int))).size = t.size := by simp
theorem mod36_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod36_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (46 : Int))).size = t.size := by simp
theorem mod36_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod36_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (47 : Int))).size = t.size := by simp
theorem mod36_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod36_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (48 : Int))).size = t.size := by simp
theorem mod36_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod36_tc_diamond (x y : Tagged 36 (Tagged 136 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod36_bignat256 : (90901175937828321097635352599821564581764637849910439502697989585662867972149 : Nat) + 64524486096865547589254786421892907698653755184154080964270531292258312788737 = 155425662034693868686890139021714472280418393034064520466968520877921180760886 := rfl
theorem mod36_arith (x y : Nat) (h : x + 36 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod36
