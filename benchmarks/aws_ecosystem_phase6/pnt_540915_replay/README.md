# Phase 6 replay of declaration 540915

The exact host checker declined `ArithmeticFunction.isCompletelyMultiplicative_liouville` at index 540915 because its proof uses `sorryAx`. The pre-fix GPU shader saw the same name while walking the proof and classified the missing slot as an unresolved constant. The corrected shader delegates this case to the host.

## Pinned input

The Windows reconstruction used PrimeNumberTheoremAnd commit `a4fb6989b07e9c76b511807ae93e33e25b820e9b`, Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, and stock Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. All 13 package revisions matched the Lake manifest. Building the root with `lake build PrimeNumberTheoremAnd` completed all 4,178 jobs. The theorem is defined with `by sorry` at lines 1787–1788 of `PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean`.

The reconstructed stream reproduced the original count of 544,714 declarations and the recorded index and name. Its root SHA-256 is `5c2d9fd9f1a0e4b92d9ca617b6ac35c9cfab6b0c2ed73899b321efc85906b442`. The historical archive has no root digest for byte-for-byte comparison. The [exact host receipt](exact_host.log) records the reconstructed input and prefix fingerprints, ordered load directories, trust option and replay command.

## Host and GPU evidence

The host checked one declaration against the environment built from the full root. The prefix contained 540,915 declarations and the first invisible constant slot was 554451. All six names in the type and 14 of the 15 distinct names in the proof resolved below that cutoff. The only absent name was `sorryAx`. The host deliberately omits its declaration from the installed constant table and recognizes use of that name as grounds to decline.

Both targeted RX 7900 XTX runs packed the full environment and dispatched this one declaration. They captured the same proof-guard lookup at expression word `202187129`. The name word `67108878` equaled the reserved `sorryAx` pin. The raw result `4294967295` is the missing-slot sentinel.

| Check | Result |
| --- | --- |
| Exact host, original prefix | Declined at 540915 for use of the sorryAx axiom |
| RX shader before fix | One GPU rejection, code 15, for the missing sorryAx slot |
| RX shader after fix | Zero GPU rejections, one delegation, host declined at 540915 |

[Pre-fix RX trace](rx_pre.log) · [Post-fix RX trace](rx_post.log) · [Historical console excerpt](../PrimeNumberTheoremAnd_rx7900xtx_console_excerpt.log)

The shader now delegates a failed lookup for the reserved `sorryAx` name at both the declaration guard and direct inference. The regression `unresolved_sorry_delegates_and_other_missing_names_reject` exercised both sites with `sorryAx` and an ordinary absent name. All four cases passed on software Vulkan. The latter name still produces rejection code 15.

## Full release check

The normal release verifier processed all 544,714 declarations with the original hybrid options. It reported 219,622 GPU verifications, zero GPU rejections and 325,092 delegations. The full input declined at its first offending declaration, 528744, for use of the sorryAx axiom. [Full release console log](rx_full.log) · [Full release JSON](rx_full.json)

The targeted trace executables have SHA-256 `4180821c0d7c10e9ee26c31f8059430083bccfc02f8d5b660b10ba3f63220311` (before) and `ba632c0a8e177ef40adf0ccb3c05d36947edf4af043dd303956f51a6a344a5d1` (after). The uninstrumented Windows release executable has SHA-256 `fc6ee1703d1d029025d1a1a1a4aadc28826b290150ab6898671291c282e6330b`.
