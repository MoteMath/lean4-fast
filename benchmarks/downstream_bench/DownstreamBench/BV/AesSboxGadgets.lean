import DownstreamBench.Prelude

namespace DownstreamBench.BV

def feistelMask (x : BitVec 16) : BitVec 16 :=
  (x.rotateLeft 3) ^^^ (x &&& 0x55aa#16)

theorem feistel_inv (k l r : BitVec 16) :
    let l1 := r
    let r1 := l ^^^ feistelMask (r ^^^ k)
    let r2 := l1
    let l2 := r1 ^^^ feistelMask (l1 ^^^ k)
    l2 = l ∧ r2 = r := by
  dsimp [feistelMask]
  bv_decide

def lfsr8Step (x : BitVec 8) : BitVec 8 :=
  let fb := (x &&& 1#8) ^^^ ((x >>> 2#8) &&& 1#8) ^^^ ((x >>> 3#8) &&& 1#8)
  (x >>> 1#8) ||| (fb <<< 7#8)

theorem lfsr8_step_bijective (a b : BitVec 8) :
    lfsr8Step a = lfsr8Step b → a = b := by
  dsimp [lfsr8Step]
  bv_decide

theorem gf2_circulant_mix (x : BitVec 8) :
    let y := x ^^^ x.rotateLeft 1 ^^^ x.rotateLeft 2
    let z := y ^^^ y.rotateLeft 3 ^^^ y.rotateLeft 6
    z = x.rotateLeft 1 ^^^ x.rotateLeft 2 ^^^ x.rotateLeft 3 ^^^
        x.rotateLeft 4 ^^^ x.rotateLeft 5 ^^^ x.rotateLeft 6 ^^^ x.rotateLeft 7 := by
  bv_decide

def byteParity (v : BitVec 8) : BitVec 8 :=
  let v1 := v ^^^ (v >>> 4#8)
  let v2 := v1 ^^^ (v1 >>> 2#8)
  (v2 ^^^ (v2 >>> 1#8)) &&& 1#8

theorem byte_parity_xor (a b : BitVec 8) :
    byteParity (a ^^^ b) = (byteParity a) ^^^ (byteParity b) := by
  dsimp [byteParity]
  bv_decide

end DownstreamBench.BV
