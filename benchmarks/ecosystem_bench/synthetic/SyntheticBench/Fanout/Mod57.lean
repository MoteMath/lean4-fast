import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod57

open SyntheticBench

@[simp] def bias_57 (n : Nat) : Nat := n + 2

theorem mod57_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (58 : Int))).size = t.size := by simp
theorem mod57_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod57_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (59 : Int))).size = t.size := by simp
theorem mod57_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod57_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (60 : Int))).size = t.size := by simp
theorem mod57_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod57_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (61 : Int))).size = t.size := by simp
theorem mod57_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod57_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (62 : Int))).size = t.size := by simp
theorem mod57_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod57_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (63 : Int))).size = t.size := by simp
theorem mod57_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod57_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (64 : Int))).size = t.size := by simp
theorem mod57_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod57_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod57_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod57_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod57_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod57_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (67 : Int))).size = t.size := by simp
theorem mod57_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod57_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (68 : Int))).size = t.size := by simp
theorem mod57_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod57_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (69 : Int))).size = t.size := by simp
theorem mod57_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod57_tc_diamond (x y : Tagged 57 (Tagged 157 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod57_bignat256 : (99534147106634245376650183732829087506517127462640814620443106761258009958932 : Nat) + 78288901287768763416873264877361047068801482293901795564845187062632393686586 = 177823048394403008793523448610190134575318609756542610185288293823890403645518 := rfl
theorem mod57_arith (x y : Nat) (h : x + 57 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod57
