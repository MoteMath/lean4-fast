/-
ConGpuProof.AxiomAudit
======================
Kernel trust audit checking `#print axioms` across all headline theorems
of the `ConGpuProof` verification package.
-/

import ConGpuProof.ArenaSpec
import ConGpuProof.ArenaOps
import ConGpuProof.StepMachine
import ConGpuProof.LratParallel
import ConGpuProof.Reductions
import ConGpuProof.Phase3Soundness
import ConGpuProof.Phase4Soundness

#print axioms ConGpuProof.pers_lookup_invariant
#print axioms ConGpuProof.pers_closed_append_invariant
#print axioms ConGpuProof.delegate_never_accepts
#print axioms ConGpuProof.stepMachine_sound
#print axioms ConGpuProof.stepMachine_hasType
#print axioms ConGpuProof.derived_clause_entailed
#print axioms ConGpuProof.gpu_parallel_lrat_unsat
#print axioms ConGpuProof.dagGuardSummary_sound
#print axioms ConGpuProof.exprSummaryWF_of_fuel
#print axioms ConGpuProof.runMachine_add
#print axioms ConGpuProof.runQuanta_eq_runMachine
#print axioms ConGpuProof.runQuanta_sound
#print axioms ConGpuProof.compactedBatch_eq_runMachine
#print axioms ConGpuProof.compactedBatch_sound
#print axioms ConGpuProof.trimLrat_sound
#print axioms ConGpuProof.remapTrimmedSteps_verify
#print axioms ConGpuProof.trimLrat_remap_sound
#print axioms ConGpuProof.nat64Pred_correct
#print axioms ConGpuProof.nat64Div_correct
#print axioms ConGpuProof.nat64Mod_correct
#print axioms ConGpuProof.nat64Shr_correct
#print axioms ConGpuProof.nat64ShlChecked_correct
#print axioms ConGpuProof.advanceEpoch_preserves_memoInv
#print axioms ConGpuProof.epochMemo_hit_sound
#print axioms ConGpuProof.quotLift_sound
#print axioms ConGpuProof.quotInd_sound
#print axioms ConGpuProof.eqRec_iota_sound
#print axioms ConGpuProof.indexedIota_sound
#print axioms ConGpuProof.verifiedPrefix_append_sound
#print axioms ConGpuProof.nat64Land_correct
#print axioms ConGpuProof.nat64Lor_correct
#print axioms ConGpuProof.nat64Xor_correct
#print axioms ConGpuProof.nat64AddChecked_correct
#print axioms ConGpuProof.nat64MulChecked_correct
#print axioms ConGpuProof.nat64PowChecked_correct
#print axioms ConGpuProof.nat64Gcd_correct
#print axioms ConGpuProof.sameHeadSpine_defeq_sound
#print axioms ConGpuProof.zeroFieldEta_defeq_sound
#print axioms ConGpuProof.zeroFieldEtaCheck_sound
#print axioms ConGpuProof.defeqEpochMemo_hit_sound
#print axioms ConGpuProof.advanceEpoch_preserves_defeqMemo
#print axioms ConGpuProof.twoEndedHybridSteal_sound
#print axioms ConGpuProof.dualArenaSnapshot_sound
#print axioms ConGpuProof.pagedArenaPage_lt_eight
#print axioms ConGpuProof.pagedArenaOffset_lt_pageCap
#print axioms ConGpuProof.pagedArenaAddr_bijective
#print axioms ConGpuProof.pagedArenaLookup_sound
#print axioms ConGpuProof.tier2BudgetPromotion_sound
#print axioms ConGpuProof.twoEndedWorkStealing_sound
#print axioms ConGpuProof.multiLimbNatAdd_correct
#print axioms ConGpuProof.multiLimbNatSub_correct
#print axioms ConGpuProof.multiLimbNatMul_correct
#print axioms ConGpuProof.multiLimbNatBeq_correct
#print axioms ConGpuProof.multiLimbNatBle_correct
#print axioms ConGpuProof.stringLitWordsEq_sound
#print axioms ConGpuProof.multiFieldStructEta_sound
#print axioms ConGpuProof.cgsnap03StatManifest_sound
#print axioms ConGpuProof.cgsnap03SplitLoad_sound
