import DownstreamBench.Prelude

namespace DownstreamBench.BV

def mux2 (sel : Bool) (a b : BitVec 32) : BitVec 32 :=
  if sel then a else b

def mux4 (s1 s0 : Bool) (x0 x1 x2 x3 : BitVec 32) : BitVec 32 :=
  mux2 s1 (mux2 s0 x3 x2) (mux2 s0 x1 x0)

theorem mux2_idem (sel : Bool) (x : BitVec 32) :
    mux2 sel x x = x := by
  dsimp [mux2]
  bv_decide

theorem mux2_not (sel : Bool) (a b : BitVec 32) :
    mux2 (!sel) a b = mux2 sel b a := by
  dsimp [mux2]
  bv_decide

theorem mux4_bitwise_eq (s1 s0 : Bool) (x0 x1 x2 x3 : BitVec 32) :
    mux4 s1 s0 x0 x1 x2 x3 =
      ((if !s1 && !s0 then x0 else 0#32) |||
       (if !s1 && s0 then x1 else 0#32)  |||
       (if s1 && !s0 then x2 else 0#32)  |||
       (if s1 && s0 then x3 else 0#32)) := by
  dsimp [mux4, mux2]
  bv_decide

def swapHalves32 (en : Bool) (x : BitVec 32) : BitVec 32 :=
  if en then (x.rotateLeft 16) else x

theorem swapHalves32_involutive (en : Bool) (x : BitVec 32) :
    swapHalves32 en (swapHalves32 en x) = x := by
  dsimp [swapHalves32]
  bv_decide

end DownstreamBench.BV
