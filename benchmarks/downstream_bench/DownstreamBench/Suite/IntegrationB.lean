import DownstreamBench.Domain.CompilerPass
import DownstreamBench.Domain.PacketParser
import DownstreamBench.Domain.IntervalAnalysis
import DownstreamBench.Domain.SchedulerModel
import DownstreamBench.Domain.RefCountModel
import DownstreamBench.Domain.MerkleProof
import DownstreamBench.Domain.SatClauseSpec
import DownstreamBench.Domain.StackMachine

namespace DownstreamBench.Suite

theorem integrationB_compiler_vm (env : Nat → Int) (e : DownstreamBench.SymExpr) :
    Domain.vmRun env (Domain.compileSym (Verify.simplifySym e)) [] = [e.eval env] :=
  Domain.compileSym_simplify_equiv env e

theorem integrationB_packet_merkle (h : Domain.PacketHdr) (l r : Domain.MerkleTree) :
    Domain.decodeHdr (Domain.encodeHdr h) = h ∧
    Domain.verifyMerklePath l.rootHash [.right r.rootHash] (Domain.MerkleTree.node l r).rootHash = true :=
  ⟨Domain.decode_encode_roundtrip h, Domain.merkle_one_step_right l r⟩

theorem integrationB_runtime_invariants (d : Domain.DequeState) (hroom : d.size < d.cap) :
    (d.pushBottom hroom).size = d.size + 1 ∧
    (Domain.ObjState.mt (-1) (by omega)).isExclusive = true :=
  ⟨Domain.push_pop_size d hroom, Domain.mt_minus1_is_exclusive (by omega)⟩

end DownstreamBench.Suite
