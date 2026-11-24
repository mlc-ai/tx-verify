-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaDequantWait
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaScoreWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.OutputDrain
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryProducerBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MemoryConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryCopyReady
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaTracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressMmaIssue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressMmaElectionReady

public section

/-! # Progress after the MMA warp has elected its issuer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {d : Wg1Mma.D}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hmax hs ht

/-- A released, pending MMA role descends to an earlier publication, once its election has
been handled. Every other issue, wait, closing arrival and return uses an actual extension. -/
theorem pending_mma_released_after_election (hp : PendingState P L X g (.mma d))
    (hRel : PTX.Step.Released L X g) (hElect : d.site ≠ .elect) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.mma d) := by
  have hX := hmax.1
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hUb : ¬ HasUb X := fun h => hSafe (.inl h)
  let hSg := sync_guarded hX hSafe
  let hOrd := Safety.reads_ordered hpre hX hs ht
  have hWr : ∀ e tag a bs, X.get e = some ⟨tag, .wr a bs⟩ → a.release = false :=
    fun _ _ _ _ he => write_no_release hX he
  have hRmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ → a.release = false :=
    fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim
  have hIssue (hSite : MmaIssueSite d.site) : False :=
    hmax.not_grows (mma_issue_extension hpre hs hX hOrd hSg hWr hRmw
      (no_thread_fence hX) hUb hp.1 hRel hp.2 hSite)
  cases hSite : d.site
  case head => exact ((MmaTracking.site_ne_head le_rfl hp.2) hSite).elim
  case elect => exact (hElect hSite).elim
  case loadTopk =>
    exact (hmax.not_grows (mma_length_extension hpre hs hX hUb hp.1 hRel hp.2 (.inl hSite))).elim
  case loadExtra =>
    exact (hmax.not_grows (mma_length_extension hpre hs hX hUb hp.1 hRel hp.2 (.inr hSite))).elim
  case qLoad k =>
    exact (hmax.not_grows (mma_query_load_extension hpre hs hX hOrd hSg hWr hRmw
      (no_thread_fence hX) hUb hp.1 hRel hp.2 hSite)).elim
  case qArrive =>
    exact (hmax.not_grows (mma_query_arrival_extension hpre hs hX hOrd hSg hWr hRmw
      (no_thread_fence hX) hUb hp.1 hRel hp.2 hSite)).elim
  case qWait => exact (no_pending_mma_query_tensor_wait hpre hmax hs ht hp hRel hSite).elim
  case qCopyWait =>
    exact (no_pending_mma_query_copy_wait hpre hmax hs ht hUb hSg hp.1 hRel hp.2 hSite).elim
  case kvWait => exact pending_mma_dequant_wait_earlier hpre hmax hs ht hp hRel hSite
  case soWait => exact pending_mma_score_wait_earlier hpre hmax hs ht hp hRel hSite
  case outBar =>
    exact (closing_arrival_not_pending hpre hmax hs hUb hp.1 hRel hp.2 hSite).elim
  case exit =>
    exact (return_not_pending_of_output hpre hmax hs ht hSafe hUb hp.1 hRel hp.2 hSite).elim
  case qCopy k => exact (hIssue (hSite.symm ▸ .queryCopy k)).elim
  case qkMma k => exact (hIssue (hSite.symm ▸ .qk k)).elim
  case pvMma k => exact (hIssue (hSite.symm ▸ .pv k)).elim
  case qCopyCommit => exact (hIssue (.commit (.inl hSite))).elim
  case qkCommit => exact (hIssue (.commit (.inr (.inl hSite)))).elim
  case pvCommit => exact (hIssue (.commit (.inr (.inr hSite)))).elim
  case qFence => exact (hIssue (.fence (.inl hSite))).elim
  case qCopyFence => exact (hIssue (.fence (.inr (.inl hSite)))).elim
  case kvFence => exact (hIssue (.fence (.inr (.inr (.inl hSite))))).elim
  case soFence => exact (hIssue (.fence (.inr (.inr (.inr hSite))))).elim

/-- Every pending, released MMA lane leads to a strictly earlier pending lane. -/
theorem pending_mma_released (hp : PendingState P L X g (.mma d)) (hRel : PTX.Step.Released L X g) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.mma d) := by
  by_cases hElect : d.site = .elect
  · exact pending_mma_election_earlier hpre hmax hs ht
      (fun h => Safety.no_unsafe_of_tracked hpre hmax.1 hs ht (.inl h)) hp hElect
  · exact pending_mma_released_after_election hpre hmax hs ht hp hRel hElect

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
