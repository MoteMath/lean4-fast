import DownstreamBench.Data.HashMapSpec
import DownstreamBench.BV.CryptoArx

namespace DownstreamBench.Domain

def hashMix32 (a b : BitVec 32) : BitVec 32 :=
  ((a.rotateLeft 5) + b) ^^^ ((b.rotateRight 7) + 0x9e3779b9#32)

inductive MerkleTree where
  | leaf : BitVec 32 → MerkleTree
  | node : MerkleTree → MerkleTree → MerkleTree
  deriving Repr, DecidableEq

def MerkleTree.rootHash : MerkleTree → BitVec 32
  | .leaf v => v
  | .node l r => hashMix32 l.rootHash r.rootHash

inductive ProofStep where
  | left : BitVec 32 → ProofStep
  | right : BitVec 32 → ProofStep
  deriving Repr, DecidableEq

def verifyMerklePath (leafHash : BitVec 32) (steps : List ProofStep) (expectedRoot : BitVec 32) : Bool :=
  let computed := steps.foldl (fun acc step =>
    match step with
    | .left sib => hashMix32 sib acc
    | .right sib => hashMix32 acc sib) leafHash
  computed == expectedRoot

theorem merkle_leaf_verify (v : BitVec 32) :
    verifyMerklePath v [] v = true := by
  simp [verifyMerklePath]

theorem merkle_one_step_right (l r : MerkleTree) :
    verifyMerklePath l.rootHash [.right r.rootHash] (MerkleTree.node l r).rootHash = true := by
  simp [verifyMerklePath, MerkleTree.rootHash]

theorem merkle_two_step_verify (a b c : MerkleTree) :
    verifyMerklePath a.rootHash [.right b.rootHash, .left c.rootHash]
      (MerkleTree.node c (MerkleTree.node a b)).rootHash = true := by
  simp [verifyMerklePath, MerkleTree.rootHash]

theorem hashMix32_comm_counterexample_guard (a : BitVec 32) :
    hashMix32 a a = ((a.rotateLeft 5) + a) ^^^ ((a.rotateRight 7) + 0x9e3779b9#32) := rfl

end DownstreamBench.Domain
