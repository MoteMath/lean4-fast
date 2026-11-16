import DownstreamBench.Prelude

namespace DownstreamBench.BV

def saddOverflow32 (a b : BitVec 32) : Bool :=
  let sum := a + b
  ((a.msb == b.msb) && (sum.msb != a.msb))

theorem saddOverflow32_comm (a b : BitVec 32) :
    saddOverflow32 a b = saddOverflow32 b a := by
  dsimp [saddOverflow32]
  bv_decide

theorem saddOverflow32_zero_right (a : BitVec 32) :
    saddOverflow32 a 0#32 = false := by
  dsimp [saddOverflow32]
  bv_decide

theorem saddOverflow32_opp_signs (a b : BitVec 32) (h : a.msb ≠ b.msb) :
    saddOverflow32 a b = false := by
  dsimp [saddOverflow32]
  bv_decide

theorem uadd_overflow_check (a b : BitVec 32) :
    ((a + b).ult a) = (0xffff_ffff#32 - a).ult b := by
  bv_decide

theorem twos_comp_min_neg (x : BitVec 16) :
    (-x == x) = (x == 0#16 || x == 0x8000#16) := by
  bv_decide

end DownstreamBench.BV
