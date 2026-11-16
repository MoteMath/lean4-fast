import DownstreamBench.Verify.WhnfDeep01
import DownstreamBench.Verify.WhnfDeep02
import DownstreamBench.Verify.DefEqMesh01
import DownstreamBench.Verify.DefEqMesh02
import DownstreamBench.Verify.TypeclassDiamond
import DownstreamBench.Verify.OmegaStress
import DownstreamBench.Verify.SimpRewriteBank
import DownstreamBench.Verify.GrindCongruence
import DownstreamBench.BV.AluCircuits
import DownstreamBench.BV.BitwiseIdentities
import DownstreamBench.BV.AesSboxGadgets
import DownstreamBench.BV.CryptoArx
import DownstreamBench.BV.SimdLanePack
import DownstreamBench.BV.StateMachineSafety
import DownstreamBench.BV.SignedOverflow
import DownstreamBench.BV.MuxNetwork

namespace DownstreamBench.Suite

theorem integrationA_bundle (a b c d : Nat) (x y : BitVec 32) :
    Verify.foldBundle a b c d = Verify.foldBundle d c b a ∧
    BV.addSubAlu true x y = x - y ∧
    BV.bswap32 (BV.bswap32 x) = x := by
  refine ⟨Verify.defeq_mesh_01 a b c d, BV.addSubAlu_spec true x y, BV.bswap32_involutive x⟩

theorem integrationA_open_whnf (a b c d e f : Nat) :
    Verify.openFoldStep 6 (a + b) (c + d) (e + f) =
      (a + b) + (c + d) + (e + f) + 36 :=
  Verify.open_whnf_fold_6 a b c d e f

end DownstreamBench.Suite
