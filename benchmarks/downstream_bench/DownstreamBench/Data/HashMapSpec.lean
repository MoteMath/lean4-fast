import DownstreamBench.Prelude

namespace DownstreamBench.Data

structure KeyTag where
  shard : Nat
  slot : Nat
  deriving Repr, DecidableEq, Hashable

def buildLookupTable (n : Nat) : Std.HashMap KeyTag Nat :=
  go n ∅
where
  go : Nat → Std.HashMap KeyTag Nat → Std.HashMap KeyTag Nat
  | 0, m => m
  | k + 1, m => go k (m.insert ⟨k % 4, k⟩ (k * 3 + 1))

theorem insert_get_same (m : Std.HashMap KeyTag Nat) (k : KeyTag) (v : Nat) :
    (m.insert k v)[k]? = some v := by
  simp

theorem insert_get_ne (m : Std.HashMap KeyTag Nat) (k₁ k₂ : KeyTag) (v : Nat)
    (h : k₁ ≠ k₂) : (m.insert k₁ v)[k₂]? = m[k₂]? := by
  simp [Std.HashMap.getElem?_insert, h]

theorem insert_contains_true (m : Std.HashMap KeyTag Nat) (k : KeyTag) (v : Nat) :
    (m.insert k v).contains k = true := by
  simp

theorem treeMap_insert_self (m : Std.TreeMap Nat String compare) (k : Nat) (v : String) :
    (m.insert k v).contains k = true := by
  simp

theorem hashSet_insert_mem (s : Std.HashSet Nat) (x : Nat) :
    x ∈ s.insert x := by
  simp

end DownstreamBench.Data
