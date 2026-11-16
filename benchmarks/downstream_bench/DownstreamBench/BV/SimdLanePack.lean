import DownstreamBench.Prelude

namespace DownstreamBench.BV

def bswap32 (x : BitVec 32) : BitVec 32 :=
  ((x &&& 0x000000ff#32) <<< 24#32) |||
  ((x &&& 0x0000ff00#32) <<< 8#32)  |||
  ((x &&& 0x00ff0000#32) >>> 8#32)  |||
  ((x &&& 0xff000000#32) >>> 24#32)

theorem bswap32_involutive (x : BitVec 32) :
    bswap32 (bswap32 x) = x := by
  dsimp [bswap32]
  bv_decide

def pack2x16 (lo hi : BitVec 16) : BitVec 32 :=
  (0#16 ++ lo) ||| ((0#16 ++ hi) <<< 16#32)

theorem pack2x16_unpack (lo hi : BitVec 16) :
    let packed := pack2x16 lo hi
    packed.truncate 16 = lo ∧ (packed >>> 16#32).truncate 16 = hi := by
  dsimp [pack2x16]
  bv_decide

def laneAdd16 (a b : BitVec 32) : BitVec 32 :=
  let lo := a.truncate 16 + b.truncate 16
  let hi := (a >>> 16#32).truncate 16 + (b >>> 16#32).truncate 16
  pack2x16 lo hi

theorem laneAdd16_comm (a b : BitVec 32) :
    laneAdd16 a b = laneAdd16 b a := by
  dsimp [laneAdd16, pack2x16]
  bv_decide

theorem laneAdd16_assoc (a b c : BitVec 32) :
    laneAdd16 (laneAdd16 a b) c = laneAdd16 a (laneAdd16 b c) := by
  dsimp [laneAdd16, pack2x16]
  bv_decide

end DownstreamBench.BV
