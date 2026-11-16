import DownstreamBench.Verify.GrindCongruence
import DownstreamBench.Verify.OmegaStress

namespace DownstreamBench.Domain

inductive ObjState where
  | st : (rc : Nat) → rc > 0 → ObjState
  | mt : (rc : Int) → rc < 0 → ObjState
  | persistent : ObjState
  deriving DecidableEq

def ObjState.isPersistent : ObjState → Bool
  | .persistent => true
  | _ => false

def ObjState.isExclusive : ObjState → Bool
  | .st 1 _ => true
  | .mt (-1) _ => true
  | _ => false

def ObjState.inc : ObjState → ObjState
  | .st rc h => .st (rc + 1) (by omega)
  | .mt rc h => .mt (rc - 1) (by omega)
  | .persistent => .persistent

def ObjState.recoverUnique : ObjState → ObjState
  | .mt (-1) _ => .st 1 (by omega)
  | s => s

theorem persistent_inc_noop : ObjState.persistent.inc = ObjState.persistent := rfl

theorem mt_unique_recovers_to_st1 (h : (-1 : Int) < 0) :
    (ObjState.mt (-1) h).recoverUnique = ObjState.st 1 (by omega) := rfl

theorem st1_is_exclusive : (ObjState.st 1 (by omega)).isExclusive = true := rfl

theorem mt_minus1_is_exclusive (h : (-1 : Int) < 0) :
    (ObjState.mt (-1) h).isExclusive = true := rfl

theorem mt_minus2_not_exclusive (h : (-2 : Int) < 0) :
    (ObjState.mt (-2) h).isExclusive = false := rfl

theorem persistent_not_exclusive : ObjState.persistent.isExclusive = false := rfl

theorem inc_not_exclusive_st (rc : Nat) (h : rc > 0) :
    (ObjState.st rc h).inc.isExclusive = false := by
  cases rc with
  | zero => omega
  | succ k => rfl

end DownstreamBench.Domain
