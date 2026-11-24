-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.AckRank
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.AckBlocked
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The acknowledgement blocker and the acknowledging threads' rank are instantiated

This file sits at the top of the proof tree, outside the layer order (as `ClcBlockedFacts.lean`
does): the progress layer sees the acknowledgement wait only through `AckBlocked` and the `ackRank`
field of `ClcWaitFacts`. The blocker comes from the protocol theorem `ack_blocked_proved`, with the
thread facts (`threadFacts`), the CLC readers' agreement (`ClcRing.allResponsesAgree`, from the
region layer's response writers) and the absence of undefined behaviour; the rank from
`Progress.ack_rank_of`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The acknowledgement blocker** (`AckBlocked`), for every consistent execution. -/
theorem ack_blocked_all {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hub : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ¬ HasUb Y) :
    ∀ Y : Execution, Consistent L kernel Prod mem0 Y → AckBlocked L Y := by
  intro Y hY
  have ht := threadFacts hpre hY
  exact ack_blocked_proved hpre hY ht (fun g k pc f h => hub Y hY ⟨(g, k), pc, f, h⟩)
    (ClcRing.allResponsesAgree hpre hY ht (Region.responseWriters hpre hY ht))

/-- **The acknowledging threads' rank** (the `ackRank` field of `ClcWaitFacts`), for every
consistent execution. -/
theorem ack_rank_all {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hub : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ¬ HasUb Y) :
    ∀ Y, Consistent L kernel Prod mem0 Y → ∀ (b : Nat) (d : ThreadD), b < L.threads →
      (∃ f : Fin 10, ClcRing.consumerSel L (b / L.block / 2) f b = true) →
      Frame.stateAt (code L) Y b (Y.tr b).length = some (some d) → d.exitOff = none →
      d.vtime L b (Y.tr b) + 1 <
        blockAt (arrivals (Bar.loc L (2 * (b / L.block / 2)) ⟨.clc, 0, false⟩) (Y.tr b) + 1) :=
  fun Y hY _ _ hb hsel hσ hex =>
    Progress.ack_rank_of (threadFacts hpre hY) (fun g k pc f h => hub Y hY ⟨(g, k), pc, f, h⟩) hb
      hsel hσ hex

end

end PTX.Kernels.Fp16Gemm8192.Proof
