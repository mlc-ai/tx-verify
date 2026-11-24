-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.AccWaits

@[expose] public section

/-! # The consumer's accumulator-full blocker, from its export

The export `ConsAccBlockedX` (`Interface.lean`) gives the blocker of a consumer at a failed poll of
its accumulator-full barrier as explicit witnesses: an open commit (obligation `commit`, rank 2), or
a pending MMA lane of the producer warp whose next event ranks at most its block's time plus `4160`
(an unelected or a working lane: `threadTime` is its vtime), or a lane whose machine stopped
without an exit (rank at most 1). Each rank is below the consumer's time `blockAt T + 4200`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow MBarrier AsyncCopy

noncomputable section

/-- **The consumer's accumulator-full blocker.** -/
theorem cons_acc_blocked_of_export {L : Launch} {mem0 : Mem0}
    (hub : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ∀ g k pc f,
      Y.get (g, k) ≠ some ⟨pc, .ub f⟩)
    (hE : ∀ Y : Execution, Consistent L kernel Prod mem0 Y →
      (∀ g k pc f, Y.get (g, k) ≠ some ⟨pc, .ub f⟩) → ConsAccBlockedX L Y) :
    ConsAccBlocked L mem0 := by
  intro Y g c pc sc before hmax hg hσ hs hlast hstate hpar
  rcases hE Y hmax.1 (hub Y hmax.1) g c pc sc before hg hσ hs hlast hstate hpar with
    ⟨i, s, r, m, hcom, htg, hnot⟩ |
    ⟨h, hh, hhc, hhw, htr, hne, d, hd, hx, hbound⟩ |
    ⟨h, hh, hhc, hhw, htr, hnex, hstopped⟩
  · refine ⟨.commit, ?_, ?_⟩
    · show ¬ ∀ i' s' r' m', Y.Commit i' s' → TcCommit.target s' r' = some m' →
        r' ∈ Y.tcNotified i'
      exact fun hall => hnot (hall i s r m hcom htg)
    · show 2 < blockAt (consCount L g (Y.tr g)) + 4200
      unfold blockAt blockSpan
      omega
  · refine ⟨.thread h, ⟨hh, fun hc => htr hc.1, hne⟩, ?_⟩
    have hT := threadTime_of hd hx
    simp only [rank, hT]
    split_ifs
    · omega
    · omega
  · refine ⟨.thread h, ⟨hh, fun hc => htr hc.1, hstopped⟩, ?_⟩
    have hT : threadTime L Y h = 0 := by
      simp only [threadTime, hnex]
    simp only [rank, hT]
    split_ifs
    · unfold blockAt blockSpan
      omega
    · unfold blockAt blockSpan
      omega

end
end PTX.Kernels.Fp16Gemm8192.Proof.Progress
