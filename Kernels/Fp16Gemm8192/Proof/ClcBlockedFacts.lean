-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.ClcWaits
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Blocker
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.ClusterAll
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The CLC response blocker is instantiated

This file sits at the top of the proof tree, outside the layer order (as `MmaFullFacts.lean` does):
the progress layer sees the CLC response blocker only through `ClcBlocked`, and this file proves it
from the protocol theorem `ClcRing.clc_blocked_of`. The thread facts (`threadFacts`) and the
cluster's exit (`clusterExitAll`) are proved; the CLC readers' values and agreement
(`ClcRing.readerValues`, `ClcRing.allResponsesAgree`) take the region layer's response writers
(`Region.responseWriters`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The CLC response blocker** (`ClcBlocked`), for every consistent execution. -/
theorem clc_blocked_proved {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ClcBlocked L Y := by
  intro Y hY g pc p acq sc before dg hg hσg hdg hlast hstate hpar
  have ht := threadFacts hpre hY
  have hrw := Region.responseWriters hpre hY ht
  exact ClcRing.clc_blocked_of hpre hY ht (ClcRing.readerValues hpre hY ht hrw)
    (ClcRing.allResponsesAgree hpre hY ht hrw) (clusterExitAll hpre hY ht) hg hσg hdg hlast
    hstate hpar

/-- **The CLC wait facts, with the response blocker proved.** The acknowledgement blocker and the
acknowledging threads' rank are the remaining premises. -/
theorem clc_wait_facts_of {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hub : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ¬ HasUb Y)
    (hack : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → AckBlocked L Y)
    (hrank : ∀ Y, Consistent L kernel Prod mem0 Y → ∀ (b : Nat) (d : ThreadD), b < L.threads →
      (∃ f : Fin 10, ClcRing.consumerSel L (b / L.block / 2) f b = true) →
      Frame.stateAt (code L) Y b (Y.tr b).length = some (some d) → d.exitOff = none →
      d.vtime L b (Y.tr b) + 1 <
        blockAt (arrivals (Bar.loc L (2 * (b / L.block / 2)) ⟨.clc, 0, false⟩) (Y.tr b) + 1)) :
    Progress.ClcWaitFacts L mem0 where
  ub := hub
  thread := fun _ hY => threadFacts hpre hY
  clcBlocked := clc_blocked_proved hpre
  ackBlocked := hack
  ackRank := hrank

end

end PTX.Kernels.Fp16Gemm8192.Proof
