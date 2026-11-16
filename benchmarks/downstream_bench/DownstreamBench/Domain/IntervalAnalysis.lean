import DownstreamBench.Verify.OmegaStress
import DownstreamBench.Algebra.LatticeTheory

namespace DownstreamBench.Domain

structure Interval where
  lo : Int
  hi : Int
  hvalid : lo ≤ hi
  deriving DecidableEq

def Interval.mem (x : Int) (iv : Interval) : Prop :=
  iv.lo ≤ x ∧ x ≤ iv.hi

def Interval.add (a b : Interval) : Interval where
  lo := a.lo + b.lo
  hi := a.hi + b.hi
  hvalid := by have := a.hvalid; have := b.hvalid; omega

def Interval.sub (a b : Interval) : Interval where
  lo := a.lo - b.hi
  hi := a.hi - b.lo
  hvalid := by have := a.hvalid; have := b.hvalid; omega

def Interval.join (a b : Interval) : Interval where
  lo := min a.lo b.lo
  hi := max a.hi b.hi
  hvalid := by have := a.hvalid; have := b.hvalid; omega

theorem Interval.add_sound (a b : Interval) (x y : Int)
    (hx : a.mem x) (hy : b.mem y) :
    (a.add b).mem (x + y) := by
  simp only [Interval.mem, Interval.add] at hx hy ⊢
  omega

theorem Interval.sub_sound (a b : Interval) (x y : Int)
    (hx : a.mem x) (hy : b.mem y) :
    (a.sub b).mem (x - y) := by
  simp only [Interval.mem, Interval.sub] at hx hy ⊢
  omega

theorem Interval.join_left (a b : Interval) (x : Int) (hx : a.mem x) :
    (a.join b).mem x := by
  simp only [Interval.mem, Interval.join] at hx ⊢
  omega

theorem Interval.join_right (a b : Interval) (x : Int) (hx : b.mem x) :
    (a.join b).mem x := by
  simp only [Interval.mem, Interval.join] at hx ⊢
  omega

end DownstreamBench.Domain
