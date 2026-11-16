import SyntheticBench.Base

namespace SyntheticBench.S4

open SyntheticBench

theorem s4_grind_cc_01 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_01 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_01 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_01 (x y z : Int) (h1 : x + y = 6) (h2 : y + z = 14) (h3 : x + z = 10) : x = 1 ∧ y = 5 ∧ z = 9 := by grind
theorem s4_grind_cc_02 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_02 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_02 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_02 (x y z : Int) (h1 : x + y = 8) (h2 : y + z = 16) (h3 : x + z = 12) : x = 2 ∧ y = 6 ∧ z = 10 := by grind
theorem s4_grind_cc_03 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_03 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_03 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_03 (x y z : Int) (h1 : x + y = 10) (h2 : y + z = 18) (h3 : x + z = 14) : x = 3 ∧ y = 7 ∧ z = 11 := by grind
theorem s4_grind_cc_04 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_04 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_04 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_04 (x y z : Int) (h1 : x + y = 12) (h2 : y + z = 20) (h3 : x + z = 16) : x = 4 ∧ y = 8 ∧ z = 12 := by grind
theorem s4_grind_cc_05 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_05 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_05 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_05 (x y z : Int) (h1 : x + y = 14) (h2 : y + z = 22) (h3 : x + z = 18) : x = 5 ∧ y = 9 ∧ z = 13 := by grind
theorem s4_grind_cc_06 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_06 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_06 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_06 (x y z : Int) (h1 : x + y = 16) (h2 : y + z = 24) (h3 : x + z = 20) : x = 6 ∧ y = 10 ∧ z = 14 := by grind
theorem s4_grind_cc_07 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_07 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_07 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_07 (x y z : Int) (h1 : x + y = 18) (h2 : y + z = 26) (h3 : x + z = 22) : x = 7 ∧ y = 11 ∧ z = 15 := by grind
theorem s4_grind_cc_08 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_08 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_08 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_08 (x y z : Int) (h1 : x + y = 20) (h2 : y + z = 28) (h3 : x + z = 24) : x = 8 ∧ y = 12 ∧ z = 16 := by grind
theorem s4_grind_cc_09 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_09 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_09 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_09 (x y z : Int) (h1 : x + y = 22) (h2 : y + z = 30) (h3 : x + z = 26) : x = 9 ∧ y = 13 ∧ z = 17 := by grind
theorem s4_grind_cc_10 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_10 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_10 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_10 (x y z : Int) (h1 : x + y = 24) (h2 : y + z = 32) (h3 : x + z = 28) : x = 10 ∧ y = 14 ∧ z = 18 := by grind
theorem s4_grind_cc_11 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_11 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_11 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_11 (x y z : Int) (h1 : x + y = 26) (h2 : y + z = 34) (h3 : x + z = 30) : x = 11 ∧ y = 15 ∧ z = 19 := by grind
theorem s4_grind_cc_12 (f g : Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : f b = c) (h3 : c = d) (h4 : g d = b) : g (f (g (f a))) = b := by grind
theorem s4_grind_list_12 (xs ys zs : List Nat) (x : Nat) : (xs ++ x :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by grind
theorem s4_grind_tree_12 (f : Nat → Nat) (t : ExprTree Nat) : (t.map f).mirror.size = t.size := by grind
theorem s4_grind_lia_12 (x y z : Int) (h1 : x + y = 28) (h2 : y + z = 36) (h3 : x + z = 32) : x = 12 ∧ y = 16 ∧ z = 20 := by grind

end SyntheticBench.S4
