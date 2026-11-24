-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryCopyReady
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarQueryLoadFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCopyWaitHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryMmaCandidate

public section

/-! # A blocked query consumer has an earlier pending producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow QueryMmaCandidate
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem before_query_commit_priority {g : Nat} {d : Wg1Mma.D}
    (h : QueryCopyHistory.BeforeCommit d.site) : priority P L g (.mma d) ≤ 141 := by
  cases hd : d.site <;> simp only [hd, QueryCopyHistory.BeforeCommit] at h
  all_goals simp only [priority, matmulTime, hd, mmaOrdinal]
  all_goals first | decide | omega

private theorem query_consumer_priority {g : Nat} {d : Machine.ThreadD}
    (h : QueryWait d true) : 141 < priority P L g d := by
  cases h with
  | copy s hState hSite =>
    simp only [hState, priority, matmulTime, hSite, mmaOrdinal]
    decide
  | gather s hState hSite =>
    simp only [hState, priority, gatherTime, hSite, tmaOrdinal]
    decide
  | dequant s hState hSite =>
    simp only [hState, priority, quantTime, hSite]
    decide

/-- The selected MMA lane is earlier when a released gather or dequantizer still waits for Q.
A committed producer would instead let the pending copy, notification or poll extend the trace. -/
theorem earlier_query_producer_of_pending
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hguarded : SyncGuarded L kernel X) {g : Nat} {d : Machine.ThreadD}
    (hp : PendingState P L X g d) (hrel : PTX.Step.Released L X g) (hWait : QueryWait d true) :
    ∃ w q, PendingState P L X w q ∧ priority P L w q < priority P L g d := by
  have hX := hmax.1
  have hub := Safety.no_ub hpre hX hs ht
  have hCta : ctaOf L g < L.grid := by
    have hB : 0 < L.block := by rw [hpre.block]; decide
    exact (Nat.div_lt_iff_lt_mul hB).2 hp.1.1
  obtain ⟨lane, _, _, hSelected⟩ := QueryMmaCandidate.select_mma hpre hX hs ht
    (fun _ hp => pending_followed hpre hX hs ht hp) hCta
  let w := ctaOf L g * L.block + 128 + lane.val
  obtain ⟨hw, hwCta, _, _⟩ := QueryMmaCandidate.lane_geometry hpre hCta lane
  have hHigher := query_consumer_priority (P := P) (L := L) (g := g) hWait
  have past {j : Nat} {q : Wg1Mma.D} (hLen : j ≤ (X.tr w).length)
      (hState : Frame.stateAt (Machine.code P L) X w j = some (some (.mma q)))
      (hPast : ¬ QueryCopyHistory.BeforeCommit q.site) : False := by
    obtain ⟨t, _, tag, p, sp, he, hst, hsite, hTarget⟩ := QueryCopyHistory.commit_before_site
      hpre hX (hs w hw).machine hw hLen hState hPast
    have hT : TcCommit.target sp 0 = some (Protocol.QueryCopy.object L (ctaOf L g)) := by
      rw [hwCta] at hTarget
      exact hTarget
    exact no_pending_query_copy_wait_of_commit hpre hmax hs ht hub hguarded
      hp.1 hrel hp.2 hWait he hst hsite hT
  rcases hSelected with ⟨j, tag, q, he, hState, hSite⟩ | ⟨q, hp', hState, hActive⟩
  · exact (past (PTX.len_of_get he).le hState (by simp [hSite, QueryCopyHistory.BeforeCommit])).elim
  · have hEarlier : priority P L w q ≤ 141 := by
      cases hActive with
      | launch s => exact (Nat.sub_le 100 _).trans (by decide)
      | dispatch => exact (show (101 : Nat) ≤ 141 by decide)
      | mma q =>
        by_cases h : QueryCopyHistory.BeforeCommit q.site
        · exact before_query_commit_priority h
        · exact (past le_rfl hState h).elim
    exact ⟨w, q, ⟨hp', hState⟩, hEarlier.trans_lt hHigher⟩

/-- The MMA query TMA wait is ready in a maximal tracked execution once its lane is released. -/
theorem no_pending_mma_query_tensor_wait
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g : Nat} {d : Wg1Mma.D} (hp : PendingState P L X g (.mma d))
    (hrel : PTX.Step.Released L X g) (hd : d.site = .qWait) : False :=
  no_pending_query_tensor_wait hpre hmax hs ht (Safety.no_ub hpre hmax.1 hs ht)
    hp.1 hrel hp.2 hd (fun _ hr => Safety.mbar_query_load_clean hpre hmax.1 hs ht hr)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
