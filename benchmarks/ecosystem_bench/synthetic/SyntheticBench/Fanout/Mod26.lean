import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod26

open SyntheticBench

@[simp] def bias_26 (n : Nat) : Nat := n + 4

theorem mod26_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (27 : Int))).size = t.size := by simp
theorem mod26_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod26_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (28 : Int))).size = t.size := by simp
theorem mod26_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod26_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (29 : Int))).size = t.size := by simp
theorem mod26_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod26_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (30 : Int))).size = t.size := by simp
theorem mod26_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod26_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (31 : Int))).size = t.size := by simp
theorem mod26_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod26_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (32 : Int))).size = t.size := by simp
theorem mod26_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod26_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (33 : Int))).size = t.size := by simp
theorem mod26_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod26_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (34 : Int))).size = t.size := by simp
theorem mod26_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod26_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (35 : Int))).size = t.size := by simp
theorem mod26_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod26_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (36 : Int))).size = t.size := by simp
theorem mod26_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod26_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (37 : Int))).size = t.size := by simp
theorem mod26_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod26_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (38 : Int))).size = t.size := by simp
theorem mod26_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod26_tc_diamond (x y : Tagged 26 (Tagged 126 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod26_bignat256 : (78519373769064819383310114044214552191551295311576181901750111072030279798999 : Nat) + 80025638717829005849052965750101970665047903838316470020715541618530046396207 = 158545012486893825232363079794316522856599199149892651922465652690560326195206 := rfl
theorem mod26_arith (x y : Nat) (h : x + 26 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod26
