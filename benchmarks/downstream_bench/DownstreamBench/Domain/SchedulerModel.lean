import DownstreamBench.BV.StateMachineSafety
import DownstreamBench.Verify.OmegaStress

namespace DownstreamBench.Domain

structure DequeState where
  top : Nat
  bottom : Nat
  cap : Nat
  hcap : cap > 0
  hle : top ≤ bottom
  hbound : bottom - top ≤ cap

def DequeState.size (d : DequeState) : Nat :=
  d.bottom - d.top

def DequeState.pushBottom (d : DequeState) (hroom : d.size < d.cap) : DequeState where
  top := d.top
  bottom := d.bottom + 1
  cap := d.cap
  hcap := d.hcap
  hle := by have := d.hle; omega
  hbound := by
    simp only [DequeState.size] at hroom
    have := d.hle
    omega

def DequeState.popBottom (d : DequeState) (hne : d.size > 0) : DequeState where
  top := d.top
  bottom := d.bottom - 1
  cap := d.cap
  hcap := d.hcap
  hle := by
    simp only [DequeState.size] at hne
    omega
  hbound := by
    have := d.hle
    have := d.hbound
    omega

def DequeState.stealTop (d : DequeState) (hne : d.size > 0) : DequeState where
  top := d.top + 1
  bottom := d.bottom
  cap := d.cap
  hcap := d.hcap
  hle := by
    simp only [DequeState.size] at hne
    omega
  hbound := by
    have := d.hle
    have := d.hbound
    omega

theorem push_pop_size (d : DequeState) (hroom : d.size < d.cap) :
    (d.pushBottom hroom).size = d.size + 1 := by
  simp only [DequeState.size, DequeState.pushBottom]
  have := d.hle
  omega

theorem steal_decreases_size (d : DequeState) (hne : d.size > 0) :
    (d.stealTop hne).size + 1 = d.size := by
  simp only [DequeState.size, DequeState.stealTop] at hne ⊢
  omega

theorem slot_index_in_bounds (cap idx : BitVec 16)
    (hmask : cap = 256#16) (hsub : idx = idx &&& 255#16) :
    idx.ult cap := by
  subst hmask
  rw [hsub]
  bv_decide

end DownstreamBench.Domain
