/-
ConGpuProof
===========
Standalone formal verification package for `con-gpu` kernel checking:
- `ConGpuProof.ArenaSpec`: 32-bit `EIdx` two-tier SoA expression arenas,
  persistent-tier immutability (`pers_lookup_invariant`, `pers_closed_append_invariant`),
  and functional Lean kernel specifications (`whnfFuel`, `defEqSpec`, `inferSpec`, `HasType`).
- `ConGpuProof.ArenaOps`: bounded scratch allocation, instantiation, and abstraction operations.
- `ConGpuProof.StepMachine`: stackless bounded-frame iterative GPU continuation machine,
  delegation safety (`delegate_never_accepts`), and soundness (`stepMachine_sound`).
- `ConGpuProof.LratParallel`: deletion-free data-parallel GPU LRAT verification soundness
  (`derived_clause_entailed`, `gpu_parallel_lrat_unsat`).
-/

import ConGpuProof.ArenaSpec
import ConGpuProof.ArenaOps
import ConGpuProof.StepMachine
import ConGpuProof.LratParallel
import ConGpuProof.Reductions
import ConGpuProof.Phase3Soundness
import ConGpuProof.Phase4Soundness
