import DownstreamBench.Prelude

namespace DownstreamBench.BV

theorem clear_lowest_set_bit (x : BitVec 32) :
    (x &&& (x - 1#32)) &&& (x &&& (-x)) = 0#32 := by
  bv_decide

theorem isolate_lowest_set_bit (x : BitVec 64) :
    (x &&& (-x)) ||| (x &&& (x - 1#64)) = x := by
  bv_decide

theorem smear_trailing_ones (x : BitVec 32) :
    (x ||| (x - 1#32)) ^^^ (x - 1#32) = (x &&& (-x)) &&& (~~~(x - 1#32) ||| x) := by
  bv_decide

theorem xor_swap_correct (a b : BitVec 32) :
    let a1 := a ^^^ b
    let b1 := b ^^^ a1
    let a2 := a1 ^^^ b1
    a2 = b ∧ b1 = a := by
  bv_decide

theorem branchless_abs_32 (x : BitVec 32) :
    let mask := x.sshiftRight 31
    (x ^^^ mask) - mask = if x.slt 0#32 then -x else x := by
  bv_decide

theorem branchless_min_16 (a b : BitVec 16) :
    let cond := if a.slt b then 0xffff#16 else 0#16
    b ^^^ ((a ^^^ b) &&& cond) = if a.slt b then a else b := by
  bv_decide

theorem de_morgan_bitvec64 (a b c : BitVec 64) :
    ~~~((a &&& b) ||| (~~~c)) = ((~~~a) ||| (~~~b)) &&& c := by
  bv_decide

theorem rot_cancel_32 (x : BitVec 32) :
    ((x.rotateLeft 13).rotateRight 13) = x := by
  bv_decide

end DownstreamBench.BV
