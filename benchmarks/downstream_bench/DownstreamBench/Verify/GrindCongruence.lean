import DownstreamBench.Data.TreeStructures
import DownstreamBench.Data.HashMapSpec

namespace DownstreamBench.Verify

theorem grind_congruence_1 (f : Nat → Nat) (a b c d : Nat)
    (h1 : a = b) (h2 : f b = c) (h3 : c = d) :
    f (f a) = f d := by
  grind

theorem grind_list_append_len (xs ys zs : List Nat) (a : Nat) :
    (xs ++ a :: ys ++ zs).length = xs.length + ys.length + zs.length + 1 := by
  grind

theorem grind_tree_mirror_map (f : Nat → Nat) (t : Data.BTree Nat) :
    (t.map f).mirror.size = t.size := by
  grind

theorem grind_hashmap_overwrite (m : Std.HashMap Data.KeyTag Nat)
    (k₁ k₂ : Data.KeyTag) (v₁ v₂ : Nat) (hne : k₁ ≠ k₂) :
    ((m.insert k₁ v₁).insert k₂ v₂)[k₁]? = some v₁ := by
  grind

theorem grind_array_swap_len (arr : Array Nat) (i j : Nat)
    (hi : i < arr.size) (hj : j < arr.size) :
    (arr.swap i j).size = arr.size := by
  grind

theorem grind_symexpr_roundtrip (env : Nat → Int) (x y : DownstreamBench.SymExpr) :
    (DownstreamBench.SymExpr.add (.neg (.neg x)) y).eval env =
      x.eval env + y.eval env := by
  simp [Int.neg_neg]

theorem grind_linear_arith (x y z : Int)
    (h1 : x + y = 10) (h2 : y + z = 20) (h3 : x + z = 14) :
    x = 2 ∧ y = 8 ∧ z = 12 := by
  grind

theorem grind_option_map_eq {α β : Type u} (f : α → β) (o : Option α) (x : α)
    (h : o = some x) : o.map f = some (f x) := by
  grind

end DownstreamBench.Verify
