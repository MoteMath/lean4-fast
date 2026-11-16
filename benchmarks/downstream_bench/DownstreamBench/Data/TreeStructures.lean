import DownstreamBench.Prelude

namespace DownstreamBench.Data

inductive BTree (α : Type u) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α
  deriving Repr, DecidableEq, BEq

def BTree.size : BTree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + l.size + r.size

def BTree.height : BTree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + max l.height r.height

def BTree.map (f : α → β) : BTree α → BTree β
  | .leaf => .leaf
  | .node l x r => .node (l.map f) (f x) (r.map f)

def BTree.mirror : BTree α → BTree α
  | .leaf => .leaf
  | .node l x r => .node r.mirror x l.mirror

def BTree.toList : BTree α → List α
  | .leaf => []
  | .node l x r => l.toList ++ [x] ++ r.toList

@[simp, grind =] theorem BTree.size_map (f : α → β) (t : BTree α) :
    (t.map f).size = t.size := by
  induction t <;> simp [BTree.map, BTree.size, *]

@[simp, grind =] theorem BTree.height_map (f : α → β) (t : BTree α) :
    (t.map f).height = t.height := by
  induction t <;> simp [BTree.map, BTree.height, *]

@[simp, grind =] theorem BTree.size_mirror (t : BTree α) :
    t.mirror.size = t.size := by
  induction t <;> simp [BTree.mirror, BTree.size, *] <;> omega

@[simp, grind =] theorem BTree.mirror_mirror (t : BTree α) :
    t.mirror.mirror = t := by
  induction t <;> simp [BTree.mirror, *]

theorem BTree.height_le_size (t : BTree α) :
    t.height ≤ t.size := by
  induction t <;> simp [BTree.height, BTree.size] <;> omega

theorem BTree.toList_length (t : BTree α) :
    t.toList.length = t.size := by
  induction t <;> simp [BTree.toList, BTree.size, *] <;> omega

theorem BTree.map_comp (g : β → γ) (f : α → β) (t : BTree α) :
    (t.map f).map g = t.map (fun x => g (f x)) := by
  induction t <;> simp [BTree.map, *]

end DownstreamBench.Data
