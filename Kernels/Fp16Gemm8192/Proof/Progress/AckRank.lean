-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # An acknowledging thread ranks below the block after its acknowledgements

A thread of an acknowledgement selector outside its exit stage, with `A` arrivals on its cluster's
acknowledgement barrier, has its next event before block `A + 1` of the rank table. Its successful
response polls are `A` plus the response it holds (`ack_exact`), and its role's count fixes the
block of its next event against those polls: a loader's empty polls (`loader_count_ok`), an MMA
thread's commits (`mma_task_count`), a consumer's accumulator polls (`cons_tiles`), and the
scheduler's response polls themselves. Every site is then arithmetic on the rank table. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {L : Launch} {X : Execution}

/-- **An acknowledging thread ranks below the block after its acknowledgements.** -/
theorem ack_rank_of (ht : ThreadFacts L X) (hub : ∀ g k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩)
    {b : Nat} {d : ThreadD} (hb : b < L.threads)
    (hsel : ∃ f : Fin 10, ClcRing.consumerSel L (b / L.block / 2) f b = true)
    (hσ : Frame.stateAt (code L) X b (X.tr b).length = some (some d)) (hex : d.exitOff = none) :
    d.vtime L b (X.tr b) + 1 <
      blockAt (arrivals (Bar.loc L (2 * (b / L.block / 2)) ⟨.clc, 0, false⟩) (X.tr b) + 1) := by
  have hE := ht.ack_exact hb hsel le_rfl hσ
  rw [List.take_length] at hE
  change d.vtime L b (X.tr b) + 1 < blockAt (arrivals (clcAck L b) (X.tr b) + 1)
  generalize arrivals (clcAck L b) (X.tr b) = A at hE ⊢
  rcases d with p | (l | m | s | c)
  · obtain ⟨site, w⟩ := p
    cases site <;> simp [ThreadD.vtime, Prologue.Site.vtime, blockAt, blockSpan] <;> omega
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht.loader_count_ok hb hσ
    simp only [ThreadD.vtime, ThreadD.clcHeld, ThreadD.exitOff] at hE hex ⊢
    generalize loaderCount L b (X.tr b) = K at h1 h2 h3 h4 h5 h6 ⊢
    generalize okPolls (clcResp L b) (X.tr b) = R at h1 h2 h3 h4 h5 h6 hE
    obtain ⟨site, mm, n, q, cp, r, x⟩ := l
    cases site <;>
      simp_all [Loader.vtime, Loader.exitOff, ringAt, blockAt, blockSpan] <;> omega
  · have hT := ht.mma_task_count hb hσ
    simp only [ThreadD.vtime, ThreadD.clcHeld, ThreadD.exitOff] at hE hex ⊢
    change okPolls (clcResp L b) (X.tr b) = _ at hT
    generalize mmaCount L b (X.tr b) = D at hT ⊢
    generalize okPolls (clcResp L b) (X.tr b) = R at hT hE
    obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
    cases site <;>
      simp_all [Mma.vtime, Mma.exitOff, ringAt, blockAt, blockSpan] <;> omega
  · simp only [ThreadD.vtime, ThreadD.clcHeld, ThreadD.exitOff, schedCount] at hE hex ⊢
    change Scheduler.vtime (okPolls (clcResp L b) (X.tr b)) s + 1 < _
    generalize okPolls (clcResp L b) (X.tr b) = R at hE ⊢
    obtain ⟨site, ap, cp, r, x⟩ := s
    cases site <;> simp_all [Scheduler.vtime, Scheduler.exitOff, blockAt, blockSpan] <;> omega
  · have hT := ht.cons_tiles hb (hub b) hσ
    simp only [ThreadD.vtime, ThreadD.clcHeld, ThreadD.exitOff] at hE hex ⊢
    change _ = okPolls (clcResp L b) (X.tr b) + _ at hT
    generalize consCount L b (X.tr b) = T at hT ⊢
    generalize okPolls (clcResp L b) (X.tr b) = R at hT hE
    obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
    cases site <;>
      simp_all [Consumer.vtime, Consumer.exitOff, Consumer.tileOpen, Consumer.holds, blockAt,
        blockSpan] <;> omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
