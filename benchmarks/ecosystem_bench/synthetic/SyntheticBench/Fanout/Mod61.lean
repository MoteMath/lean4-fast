import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod61

open SyntheticBench

@[simp] def bias_61 (n : Nat) : Nat := n + 6

theorem mod61_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (62 : Int))).size = t.size := by simp
theorem mod61_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod61_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (63 : Int))).size = t.size := by simp
theorem mod61_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod61_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (64 : Int))).size = t.size := by simp
theorem mod61_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod61_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod61_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod61_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod61_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod61_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (67 : Int))).size = t.size := by simp
theorem mod61_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod61_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (68 : Int))).size = t.size := by simp
theorem mod61_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod61_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (69 : Int))).size = t.size := by simp
theorem mod61_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod61_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (70 : Int))).size = t.size := by simp
theorem mod61_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod61_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (71 : Int))).size = t.size := by simp
theorem mod61_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod61_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (72 : Int))).size = t.size := by simp
theorem mod61_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod61_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (73 : Int))).size = t.size := by simp
theorem mod61_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod61_tc_diamond (x y : Tagged 61 (Tagged 161 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod61_bignat256 : (92907659050408026521278601001280437829974567422667806847396917235696701703840 : Nat) + 83667649163114999651544830605714204209473517065028859574618484784251427695758 = 176575308213523026172823431606994642039448084487696666422015402019948129399598 := rfl
theorem mod61_arith (x y : Nat) (h : x + 61 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod61
