-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.IndexWaitBlocker
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.SoftmaxVote
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingDealloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaCompletionShape
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.SoftmaxPvWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MemoryConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressBulkWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Arrivals
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Barrier
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0ElectionReady
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0OutputIssue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Reads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0RescaleStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0TmemLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Writes
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmemWholeWords

public section

/-! # Progress for all released softmax sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- The released softmax sites either extend the actual trace or descend to an earlier lane. -/
theorem pending_softmax_released {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g (.wg0 d)) (hRel : PTX.Step.Released L X g) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.wg0 d) := by
  have hX := hmax.1
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hub : ¬ HasUb X := fun h => hSafe (.inl h)
  let hSg := sync_guarded hX hSafe
  let hOrd := Safety.reads_ordered hpre hX hs ht
  have hWr : ∀ e tag a bs, X.get e = some ⟨tag, .wr a bs⟩ → a.release = false :=
    fun _ _ _ _ he => write_no_release hX he
  have hRmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ → a.release = false :=
    fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim
  have input (h : d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra) : False :=
    hmax.not_grows (softmax_input_extension hpre hX hs hub hp.1 hRel hp.2 h)
  have arrival (w : SoftmaxArrival) (h : d.site = w.site) : False :=
    hmax.not_grows (softmax_arrival_extension hpre hs hX hOrd hSafe hp.1 hRel hp.2 w h)
  have bar (h : Wg0BarrierTrace.Bar9Site d.site ∨ d.site = .pairBar) : False :=
    hmax.not_grows (softmax_named_bar_extension hpre hs hX hub hp.1 hRel hp.2 h)
  have load (h : SoftmaxLoad d.site) : False :=
    hmax.not_grows (softmax_tmem_load_extension hpre hs hX hSg (mma_layout_injective hpre hX hs ht)
      (fun ⟨_, _⟩ _ _ he => tmem_wrote_bytes hpre hX hs ht he) hub hp.1 hRel hp.2 h)
  have read (h : SoftmaxReadSite d.site) : False :=
    hmax.not_grows (softmax_read_extension hpre hs hX hSg hub hp.1 hRel hp.2 h)
  have write (h : SoftmaxWriteSite d.site) : False :=
    hmax.not_grows (softmax_write_extension hpre hs hX ht hub hp.1 hRel hp.2 h)
  have quiet (h : SoftmaxQuietSite d.site) : False :=
    hmax.not_grows (softmax_quiet_extension hs hX hOrd hSafe hp.1 hRel hp.2 h)
  have tc {k : TcKind} (h : SoftmaxTcSite d.site k) : False :=
    hmax.not_grows (softmax_tc_control_extension hpre hs hX hOrd hSg hWr hRmw (no_thread_fence hX)
      hub hp.1 hRel hp.2 h)
  cases hS : d.site
  case sink => exact (input (.inl hS)).elim
  case lenOrig => exact (input (.inr (.inl hS))).elim
  case lenExtra => exact (input (.inr (.inr hS))).elim
  case bulkWait => exact (hmax.not_grows (bulk_wait_extension hX hs hub hp.1 hRel hp.2 hS)).elim
  case lastStore => exact (arrival .lastStore hS).elim
  case wg0Sync => exact (bar (.inl (hS.symm ▸ trivial))).elim
  case maskReady => exact pending_index_ready_earlier hpre hmax hs ht hub hp hRel (.softmax hS)
  case qkDone =>
    obtain ⟨h, q, _, hPend, hLt⟩ := pending_softmax_qk_earlier hpre hmax hs ht hSg hp hRel hS
    exact ⟨h, q, hPend, hLt⟩
  case fenceLoad => exact (tc (by rw [hS]; exact SoftmaxTcSite.fenceLoad)).elim
  case scoreLoad arm part => exact (load (hS.symm ▸ .score arm part)).elim
  case scoreWait => exact (tc (by rw [hS]; exact SoftmaxTcSite.scoreWait)).elim
  case fenceBefore => exact (tc (by rw [hS]; exact SoftmaxTcSite.fenceBefore)).elim
  case maskRead => exact (read (hS.symm ▸ .maskRead)).elim
  case exchStore i => exact (write (hS.symm ▸ .exchStore i)).elim
  case pairBar => exact (bar (.inr hS)).elim
  case peerRead i => exact (read (hS.symm ▸ .peerRead i)).elim
  case rowMax => exact (write (hS.symm ▸ .rowMax)).elim
  case wg0Sync2 => exact (bar (.inl (hS.symm ▸ trivial))).elim
  case validFree => exact (arrival .validFree hS).elim
  case maxRead => exact (read (hS.symm ▸ .maxRead)).elim
  case rescaleVote => exact pending_softmax_vote_earlier hpre hmax hs ht hub hp hS
  case pStore i => exact (write (hS.symm ▸ .pStore i)).elim
  case rescaleFence => exact (tc (by rw [hS]; exact SoftmaxTcSite.rescaleFence)).elim
  case rescaleLoad j => exact (load (hS.symm ▸ .rescale j)).elim
  case rescaleWait j => exact (tc (by rw [hS]; exact SoftmaxTcSite.rescaleWait j)).elim
  case rescaleStore j =>
    exact (hmax.not_grows (softmax_rescale_store_extension hpre hs hX hub hp.1 hRel hp.2 hS)).elim
  case rescaleWaitSt j => exact (tc (by rw [hS]; exact SoftmaxTcSite.rescaleWaitSt j)).elim
  case rescaleFenceB => exact (tc (by rw [hS]; exact SoftmaxTcSite.rescaleFenceB)).elim
  case soFence => exact (quiet (hS.symm ▸ .soFence)).elim
  case soReady => exact (arrival .soReady hS).elim
  case lseBar => exact (bar (.inl (hS.symm ▸ trivial))).elim
  case lseStore0 => exact (write (hS.symm ▸ .lseStore0)).elim
  case lseBar2 => exact (bar (.inl (hS.symm ▸ trivial))).elim
  case lseRead => exact (read (hS.symm ▸ .lseRead)).elim
  case lseStore => exact (write (hS.symm ▸ .lseStore)).elim
  case svDone =>
    obtain ⟨h, q, _, hPend, hLt⟩ := pending_softmax_pv_earlier hpre hmax hs ht hSg hp hRel hS
    exact ⟨h, q, hPend, hLt⟩
  case fenceEpilogue => exact (tc (by rw [hS]; exact SoftmaxTcSite.fenceEpilogue)).elim
  case oLoad j => exact (load (hS.symm ▸ .output j)).elim
  case oWait j => exact (tc (by rw [hS]; exact SoftmaxTcSite.oWait j)).elim
  case oStage j k => exact (write (hS.symm ▸ .oStage j k)).elim
  case stageFence j => exact (quiet (hS.symm ▸ .stageFence j)).elim
  case epiBar j => exact (bar (.inl (hS.symm ▸ trivial))).elim
  case elect j =>
    exact (hmax.not_grows (softmax_election_extension hpre hs hX ht hub hp.1 hRel hp.2 hS)).elim
  case tmaStore j =>
    exact (hmax.not_grows (softmax_output_issue_extension hpre hs hX hOrd hSg hWr hRmw
      (no_thread_fence hX) hub hp.1 hRel hp.2 hS)).elim
  case commit => exact (quiet (hS.symm ▸ .commit)).elim
  case everyone => exact (closing_arrival_not_pending hpre hmax hs hub hp.1 hRel hp.2 hS).elim
  case exit => exact (dealloc_not_pending hpre hmax hs hub hp.1 hRel hp.2 hS).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
