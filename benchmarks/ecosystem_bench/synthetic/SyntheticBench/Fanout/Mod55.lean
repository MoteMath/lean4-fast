import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod55

open SyntheticBench

@[simp] def bias_55 (n : Nat) : Nat := n + 0

theorem mod55_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (56 : Int))).size = t.size := by simp
theorem mod55_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod55_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (57 : Int))).size = t.size := by simp
theorem mod55_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod55_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (58 : Int))).size = t.size := by simp
theorem mod55_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod55_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (59 : Int))).size = t.size := by simp
theorem mod55_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod55_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (60 : Int))).size = t.size := by simp
theorem mod55_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod55_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (61 : Int))).size = t.size := by simp
theorem mod55_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod55_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (62 : Int))).size = t.size := by simp
theorem mod55_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod55_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (63 : Int))).size = t.size := by simp
theorem mod55_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod55_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (64 : Int))).size = t.size := by simp
theorem mod55_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod55_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod55_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod55_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod55_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod55_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (67 : Int))).size = t.size := by simp
theorem mod55_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod55_tc_diamond (x y : Tagged 55 (Tagged 155 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod55_bignat256 : (73899368825418305951581779714124775763218664844360541473402849196502805275598 : Nat) + 104547549659424694152291677397663105080035207546605040593494220413248171165456 = 178446918484843000103873457111787880843253872390965582066897069609750976441054 := rfl
theorem mod55_arith (x y : Nat) (h : x + 55 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod55
