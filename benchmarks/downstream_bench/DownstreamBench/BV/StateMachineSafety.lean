import DownstreamBench.Prelude

namespace DownstreamBench.BV

def grantMask (req : BitVec 8) : BitVec 8 :=
  req &&& (-req)

theorem grantMask_one_hot (req : BitVec 8) :
    let g := grantMask req
    g &&& (g - 1#8) = 0#8 := by
  dsimp [grantMask]
  bv_decide

theorem grantMask_subset_req (req : BitVec 8) :
    (grantMask req &&& req) = grantMask req := by
  dsimp [grantMask]
  bv_decide

theorem grantMask_nonzero_when_req (req : BitVec 8) (h : req ≠ 0#8) :
    grantMask req ≠ 0#8 := by
  dsimp [grantMask]
  bv_decide

theorem ring_ptr_mask_invariant (head count : BitVec 16) (idx : BitVec 16)
    (hidx : idx.ult count) (hcount : count.ule 64#16) :
    ((head + idx) &&& 63#16).ult 64#16 := by
  bv_decide

theorem masked_write_preserves_high (reg val mask : BitVec 32) :
    let next := (reg &&& ~~~mask) ||| (val &&& mask)
    (next &&& ~~~mask) = (reg &&& ~~~mask) ∧ (next &&& mask) = (val &&& mask) := by
  bv_decide

end DownstreamBench.BV
