import Std

theorem badBv (x : BitVec 16) : x + 1#16 = x := by
  bv_decide
