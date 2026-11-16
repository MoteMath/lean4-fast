import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod35

open SyntheticBench

@[simp] def bias_35 (n : Nat) : Nat := n + 2

theorem mod35_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (36 : Int))).size = t.size := by simp
theorem mod35_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod35_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (37 : Int))).size = t.size := by simp
theorem mod35_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod35_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (38 : Int))).size = t.size := by simp
theorem mod35_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod35_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (39 : Int))).size = t.size := by simp
theorem mod35_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod35_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (40 : Int))).size = t.size := by simp
theorem mod35_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod35_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (41 : Int))).size = t.size := by simp
theorem mod35_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod35_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (42 : Int))).size = t.size := by simp
theorem mod35_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod35_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (43 : Int))).size = t.size := by simp
theorem mod35_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod35_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (44 : Int))).size = t.size := by simp
theorem mod35_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod35_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (45 : Int))).size = t.size := by simp
theorem mod35_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod35_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (46 : Int))).size = t.size := by simp
theorem mod35_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod35_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (47 : Int))).size = t.size := by simp
theorem mod35_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod35_tc_diamond (x y : Tagged 35 (Tagged 135 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod35_bignat256 : (107031809106549400240993896842641385673603043890640913170783167481016286922002 : Nat) + 77653810282693512953825441814350596322352723098901870270553093617371039047532 = 184685619389242913194819338656991981995955766989542783441336261098387325969534 := rfl
theorem mod35_arith (x y : Nat) (h : x + 35 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod35
