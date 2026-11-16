import SyntheticBench.Base

namespace SyntheticBench.S5

def alu32 (op : BitVec 2) (a b : BitVec 32) : BitVec 32 :=
  if op == 0#2 then a + b
  else if op == 1#2 then a - b
  else if op == 2#2 then a ^^^ b
  else a &&& b

theorem bv_add_sub_cancel32 (a b : BitVec 32) : (a + b) - b = a := by bv_decide
theorem bv_neg_twos32 (x : BitVec 32) : -x = ~~~x + 1#32 := by bv_decide
theorem bv_xor_swap32 (a b : BitVec 32) :
    let a1 := a ^^^ b
    let b1 := b ^^^ a1
    let a2 := a1 ^^^ b1
    a2 = b ∧ b1 = a := by bv_decide
theorem bv_demorgan32 (a b : BitVec 32) : ~~~(a &&& b) = ~~~a ||| ~~~b := by bv_decide
theorem bv_demorgan64 (a b : BitVec 64) : ~~~(a ||| b) = ~~~a &&& ~~~b := by bv_decide
theorem bv_rotl_rotr32 (x : BitVec 32) : (x.rotateLeft 13).rotateRight 13 = x := by bv_decide
theorem bv_rotl_rotr64 (x : BitVec 64) : (x.rotateLeft 29).rotateRight 29 = x := by bv_decide
theorem bv_rotl_compose32 (x : BitVec 32) :
    (x.rotateLeft 7).rotateLeft 9 = x.rotateLeft 16 := by bv_decide
theorem bv_mask_idemp32 (x m : BitVec 32) : (x &&& m) &&& m = x &&& m := by bv_decide
theorem bv_clear_lowbits64 (x : BitVec 64) :
    (x &&& ~~~0xFF#64) &&& 0xFF#64 = 0#64 := by bv_decide
theorem bv_avg_floor32 (x y : BitVec 32) :
    (x &&& y) + ((x ^^^ y) >>> 1#32) =
      (((0#1 ++ x) + (0#1 ++ y)) >>> 1).truncate 32 := by bv_decide
theorem bv_carry_save32 (a b c : BitVec 32) :
    let s := a ^^^ b ^^^ c
    let k := ((a &&& b) ||| (b &&& c) ||| (a &&& c)) <<< 1#32
    s + k = a + b + c := by bv_decide
def bswap32 (y : BitVec 32) : BitVec 32 :=
  ((y &&& 0x000000FF#32) <<< 24) |||
  ((y &&& 0x0000FF00#32) <<< 8)  |||
  ((y &&& 0x00FF0000#32) >>> 8)  |||
  ((y &&& 0xFF000000#32) >>> 24)

theorem bv_bswap32_inv (x : BitVec 32) :
    bswap32 (bswap32 x) = x := by
  dsimp [bswap32]; bv_decide
theorem bv_mux_sel32 (s : Bool) (a b : BitVec 32) :
    (if s then a else b) = (if !s then b else a) := by bv_decide
theorem bv_alu_add_comm32 (a b : BitVec 32) :
    alu32 0#2 a b = alu32 0#2 b a := by
  dsimp [alu32]; bv_decide
theorem bv_alu_sub_anti32 (a b : BitVec 32) :
    alu32 1#2 a b = -(alu32 1#2 b a) := by
  dsimp [alu32]; bv_decide
theorem bv_alu_xor_assoc32 (a b c : BitVec 32) :
    alu32 2#2 (alu32 2#2 a b) c = alu32 2#2 a (alu32 2#2 b c) := by
  dsimp [alu32]; bv_decide
theorem bv_alu_and_idem32 (a : BitVec 32) :
    alu32 3#2 a a = a := by
  dsimp [alu32]; bv_decide
theorem bv_parity_fold32 (x : BitVec 32) :
    let p1 := x ^^^ (x >>> 16)
    let p2 := p1 ^^^ (p1 >>> 8)
    let p3 := p2 ^^^ (p2 >>> 4)
    let p4 := p3 ^^^ (p3 >>> 2)
    let p5 := p4 ^^^ (p4 >>> 1)
    (p5 &&& 1#32) = ((p4 &&& 3#32) ^^^ ((p4 &&& 3#32) >>> 1)) &&& 1#32 := by
  bv_decide
theorem bv_pop_zero_detect64 (x : BitVec 64) :
    (x == 0#64) = ((~~~x) == 0xFFFFFFFFFFFFFFFF#64) := by bv_decide
theorem bv_sub_borrow64 (a b : BitVec 64) :
    a - b = ~~~((~~~a) + b) := by bv_decide
theorem bv_add_overflow_wrap32 (a : BitVec 32) :
    (a + 0xFFFFFFFF#32) + 1#32 = a := by bv_decide
theorem bv_mask_or_absorb64 (a b : BitVec 64) :
    (a ||| b) &&& a = a := by bv_decide
theorem bv_shift_mask32 (x : BitVec 32) :
    ((x <<< 4) >>> 4) = (x &&& 0x0FFFFFFF#32) := by bv_decide

end SyntheticBench.S5
