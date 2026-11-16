import DownstreamBench.Suite.IntegrationA
import DownstreamBench.Suite.IntegrationB

namespace DownstreamBench

theorem downstream_suite_verified
    (a b c d : Nat) (x y : BitVec 32) (env : Nat → Int) (e : SymExpr) (h : Domain.PacketHdr) :
    Verify.foldBundle a b c d = Verify.foldBundle d c b a ∧
    BV.addSubAlu true x y = x - y ∧
    Domain.vmRun env (Domain.compileSym (Verify.simplifySym e)) [] = [e.eval env] ∧
    Domain.decodeHdr (Domain.encodeHdr h) = h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Suite.integrationA_bundle a b c d x y).1
  · exact (Suite.integrationA_bundle a b c d x y).2.1
  · exact Suite.integrationB_compiler_vm env e
  · exact (Suite.integrationB_packet_merkle h (.leaf 1#32) (.leaf 2#32)).1

end DownstreamBench
