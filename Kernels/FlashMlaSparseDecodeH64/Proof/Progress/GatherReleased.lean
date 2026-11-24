-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.IndexWaitBlocker
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.RawFreeWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LastStoreWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.OutputDrain
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryProducerBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MemoryConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressRingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressTmaElectionReady
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressTmaIssue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressTmaRead

public section

/-! # Progress for all released gather producer sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- A pending, released gather lane in a maximal followed execution has an earlier pending
dependency. Its gather issues, publications and reads extend directly. -/
theorem pending_gather_released {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Tma.D} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g (.tma d)) (hRel : PTX.Step.Released L X g) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.tma d) := by
  have hX := hmax.1
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hub : ¬ HasUb X := fun h => hSafe (.inl h)
  let hSg := sync_guarded hX hSafe
  let hOrd := Safety.reads_ordered hpre hX hs ht
  have hRead (hSite : GatherRead d.site) : False :=
    hmax.not_grows (tma_read_extension hpre hs hX hSafe hp.1 hRel hp.2 hSite)
  have hPublish (hSite : RingArrival (.tma d)) : False :=
    hmax.not_grows (ring_arrival_extension hpre hs hX hOrd hSg
      (fun _ _ _ _ he => write_no_release hX he)
      (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
      (no_thread_fence hX) hub hp.1 hRel hp.2 hSite)
  cases hSite : d.site
  case elect =>
    obtain ⟨h, q, _, hPend, hLt⟩ := pending_tma_election_earlier hpre hmax hs ht hub hp hSite
    exact ⟨h, q, hPend, hLt⟩
  case lenOrig => exact (hRead (hSite.symm ▸ .lenOrig)).elim
  case lenExtra => exact (hRead (hSite.symm ▸ .lenExtra)).elim
  case waitQ =>
    exact earlier_query_producer_of_pending hpre hmax hs ht hSg hp hRel (.gather d rfl hSite)
  case waitLast =>
    obtain ⟨h, q, _, hP, hState, hLt⟩ := pending_last_store_earlier hpre hmax hs ht hub
      (fun _ h => pending_followed hpre hX hs ht h) hp.1 hRel hp.2 hSite
    exact ⟨h, q, ⟨hP, hState⟩, hLt⟩
  case waitCoord =>
    exact pending_index_ready_earlier hpre hmax hs ht hub hp hRel (.gather hSite)
  case waitFree =>
    exact pending_raw_free_earlier hpre hmax hs ht hub hp hRel hSite
  case coord k j => exact (hRead (hSite.symm ▸ .coord k j)).elim
  case issue k =>
    exact (hmax.not_grows (tma_issue_extension hpre hs hX hOrd hSafe hp.1 hRel hp.2 hSite)).elim
  case rawReady => exact (hPublish (.rawReady hSite)).elim
  case coordFree => exact (hPublish (.coordFree hSite)).elim
  case barrier =>
    exact (closing_arrival_not_pending hpre hmax hs hub hp.1 hRel hp.2 hSite).elim
  case exit =>
    exact (return_not_pending_of_output hpre hmax hs ht hSafe hub hp.1 hRel hp.2 hSite).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
