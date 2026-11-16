import DownstreamBench.Prelude

namespace DownstreamBench.BV

def addSubAlu (sub : Bool) (a b : BitVec 32) : BitVec 32 :=
  if sub then a + (~~~b) + 1#32 else a + b

theorem addSubAlu_spec (sub : Bool) (a b : BitVec 32) :
    addSubAlu sub a b = if sub then a - b else a + b := by
  dsimp [addSubAlu]
  bv_decide

theorem alu_zero_flag (a b : BitVec 32) :
    (a - b == 0#32) = (a == b) := by
  bv_decide

theorem alu_neg_add_cancel (a b : BitVec 32) :
    (a + b) + (-b) = a := by
  bv_decide

theorem alu_neg_identity (x : BitVec 32) :
    -x = ~~~x + 1#32 := by
  bv_decide

theorem alu_sub_via_add (a b : BitVec 64) :
    a - b = ~~~((~~~a) + b) := by
  bv_decide

theorem alu_avg_floor (x y : BitVec 32) :
    (x &&& y) + ((x ^^^ y) >>> 1#32) =
      (((0#1 ++ x) + (0#1 ++ y)) >>> 1).truncate 32 := by
  bv_decide

theorem alu_carry_save_step (a b c : BitVec 16) :
    let sum := a ^^^ b ^^^ c
    let carry := ((a &&& b) ||| (b &&& c) ||| (a &&& c)) <<< 1#16
    sum + carry = a + b + c := by
  bv_decide

end DownstreamBench.BV
