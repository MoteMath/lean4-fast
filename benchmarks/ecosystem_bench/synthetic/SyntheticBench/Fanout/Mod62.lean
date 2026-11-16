import SyntheticBench.Base

namespace SyntheticBench.Fanout.Mod62

open SyntheticBench

@[simp] def bias_62 (n : Nat) : Nat := n + 7

theorem mod62_simp_01 (t : ExprTree Int) : (t.mirror.map (· + (63 : Int))).size = t.size := by simp
theorem mod62_grind_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by grind
theorem mod62_simp_02 (t : ExprTree Int) : (t.mirror.map (· + (64 : Int))).size = t.size := by simp
theorem mod62_grind_02 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 2 = c + 2 := by grind
theorem mod62_simp_03 (t : ExprTree Int) : (t.mirror.map (· + (65 : Int))).size = t.size := by simp
theorem mod62_grind_03 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 3 = c + 3 := by grind
theorem mod62_simp_04 (t : ExprTree Int) : (t.mirror.map (· + (66 : Int))).size = t.size := by simp
theorem mod62_grind_04 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 4 = c + 4 := by grind
theorem mod62_simp_05 (t : ExprTree Int) : (t.mirror.map (· + (67 : Int))).size = t.size := by simp
theorem mod62_grind_05 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 5 = c + 5 := by grind
theorem mod62_simp_06 (t : ExprTree Int) : (t.mirror.map (· + (68 : Int))).size = t.size := by simp
theorem mod62_grind_06 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 6 = c + 6 := by grind
theorem mod62_simp_07 (t : ExprTree Int) : (t.mirror.map (· + (69 : Int))).size = t.size := by simp
theorem mod62_grind_07 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 7 = c + 7 := by grind
theorem mod62_simp_08 (t : ExprTree Int) : (t.mirror.map (· + (70 : Int))).size = t.size := by simp
theorem mod62_grind_08 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 8 = c + 8 := by grind
theorem mod62_simp_09 (t : ExprTree Int) : (t.mirror.map (· + (71 : Int))).size = t.size := by simp
theorem mod62_grind_09 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 9 = c + 9 := by grind
theorem mod62_simp_10 (t : ExprTree Int) : (t.mirror.map (· + (72 : Int))).size = t.size := by simp
theorem mod62_grind_10 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 10 = c + 10 := by grind
theorem mod62_simp_11 (t : ExprTree Int) : (t.mirror.map (· + (73 : Int))).size = t.size := by simp
theorem mod62_grind_11 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 11 = c + 11 := by grind
theorem mod62_simp_12 (t : ExprTree Int) : (t.mirror.map (· + (74 : Int))).size = t.size := by simp
theorem mod62_grind_12 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : f b = c) : f a + 12 = c + 12 := by grind
theorem mod62_tc_diamond (x y : Tagged 62 (Tagged 162 Nat)) : SB_Magma.op x y = SB_Magma.op y x := SB_CommMonoid.op_comm x y
theorem mod62_bignat256 : (76777025881686947377920056758460616738136161381937333179311739340343282753987 : Nat) + 70538324977287034286974175213256515585774549150281070268354369203212410988579 = 147315350858973981664894231971717132323910710532218403447666108543555693742566 := rfl
theorem mod62_arith (x y : Nat) (h : x + 62 ≤ y) : x ≤ y := by omega

end SyntheticBench.Fanout.Mod62
