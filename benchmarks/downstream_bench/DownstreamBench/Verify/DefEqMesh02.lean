import DownstreamBench.Verify.DefEqMesh01
import DownstreamBench.Data.HashMapSpec

namespace DownstreamBench.Verify

structure BoundedVec (α : Type u) (cap : Nat) where
  data : Array α
  hcap : data.size ≤ cap

def BoundedVec.empty (cap : Nat) : BoundedVec α cap :=
  ⟨#[], Nat.zero_le _⟩

def BoundedVec.pushIfRoom {cap : Nat} (v : BoundedVec α cap) (x : α)
    (h : v.data.size < cap) : BoundedVec α cap :=
  ⟨v.data.push x, by rw [Array.size_push]; exact h⟩

def BoundedVec.castCap {cap₁ cap₂ : Nat} (h : cap₁ = cap₂) (v : BoundedVec α cap₁) :
    BoundedVec α cap₂ :=
  ⟨v.data, h ▸ v.hcap⟩

theorem BoundedVec.castCap_rfl {cap : Nat} (v : BoundedVec α cap) :
    v.castCap rfl = v := rfl

theorem BoundedVec.castCap_trans {c₁ c₂ c₃ : Nat} (h₁ : c₁ = c₂) (h₂ : c₂ = c₃)
    (v : BoundedVec α c₁) :
    (v.castCap h₁).castCap h₂ = v.castCap (h₁.trans h₂) := by
  subst h₁; subst h₂; rfl

def depSigmaPack (n : Nat) : (k : Nat) × Fin (k + 1) :=
  ⟨n, ⟨n, Nat.lt_succ_self n⟩⟩

theorem depSigmaPack_fst (n : Nat) : (depSigmaPack n).1 = n := rfl

theorem depSigmaPack_val (n : Nat) : (depSigmaPack n).2.val = n := rfl

theorem subtype_transport_defeq (n m : Nat) (h : n = m)
    (x : { k : Nat // k < n + 1 }) :
    (h ▸ x).1 = x.1 := by
  subst h
  rfl

theorem hashmap_key_defeq (m : Std.HashMap Data.KeyTag Nat) (a b v : Nat) :
    (m.insert ⟨a, b⟩ v)[Data.KeyTag.mk a b]? = some v := by
  exact Data.insert_get_same m ⟨a, b⟩ v

end DownstreamBench.Verify
