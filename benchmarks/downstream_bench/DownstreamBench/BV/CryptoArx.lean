import DownstreamBench.Prelude

namespace DownstreamBench.BV

def speckX (x y k : BitVec 32) : BitVec 32 :=
  (x.rotateRight 8 + y) ^^^ k

def speckY (x y k : BitVec 32) : BitVec 32 :=
  y.rotateLeft 3 ^^^ speckX x y k

theorem speck_round_invertible (x y k : BitVec 32) :
    let x' := speckX x y k
    let y' := speckY x y k
    let y0 := (y' ^^^ x').rotateRight 3
    let x0 := ((x' ^^^ k) - y0).rotateLeft 8
    x0 = x ∧ y0 = y := by
  dsimp [speckX, speckY]
  bv_decide

theorem chacha_quarter_invertible (a b c d : BitVec 16) :
    let a1 := a + b
    let d1 := (d ^^^ a1).rotateLeft 8
    let c1 := c + d1
    let b1 := (b ^^^ c1).rotateLeft 7
    let b0 := b1.rotateRight 7 ^^^ c1
    let c0 := c1 - d1
    let d0 := d1.rotateRight 8 ^^^ a1
    let a0 := a1 - b0
    a0 = a ∧ b0 = b ∧ c0 = c ∧ d0 = d := by
  bv_decide

theorem arx_modadd_xor_lsb (x y : BitVec 32) :
    ((x + y) &&& 1#32) = ((x ^^^ y) &&& 1#32) := by
  bv_decide

end DownstreamBench.BV
