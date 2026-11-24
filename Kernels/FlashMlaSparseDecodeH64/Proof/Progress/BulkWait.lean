-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressBulkWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Lemmas.Step.BulkWaitReady

public section

/-! # The opening bulk-group wait covers no store or copy -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
include hpre hX hs

private theorem no_earlier_store (ht : Frame.Tracked (Machine.code P L) X) {g i j : Nat}
    (hLt : j < i) (hLen : i ≤ (X.tr g).length) {d : Wg0.D} (hWait : d.site = .bulkWait)
    (hSub : d.sub = 0) (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    {a : Nat} {sp : TensorStore.Spec} (hIssue : X.TensorStoreIssue (g, j) a sp) : False := by
  obtain ⟨q, tile, hQState, hQSite⟩ := GlobalWrites.outputTile_site hs hX ht hIssue
  obtain ⟨tag, he⟩ := hIssue
  have hg := Frame.lt_of_get hX he
  have hRank := Wg0ProbabilityUnique.rank_strict_of_counted hpre hX (hs g hg).machine ht
    he rfl hLen hQState hState hLt
  simp only [Bound.rank, Bound.wg0Rank, Bound.wg0Block, Bound.wg0Ordinal, hQSite, hWait,
    hSub, Nat.sub_zero] at hRank
  have hMono := Nat.sub_le (Wg0.blocksOf P L g) q.block
  omega

/-- A bulk wait from the opening softmax site has no queued operation, hence no dependency. -/
theorem opening_bulk_wait_ready (ht : Frame.Tracked (Machine.code P L) X) {g i tag : Nat}
    {d : Wg0.D} (hEvent : X.get (g, i) = some ⟨tag, .bulkWait .read 0⟩) (hWait : d.site = .bulkWait)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) :
    Ready L X (g, i) := by
  intro n hn
  simp only [Needs, hEvent, KindNeeds, groupNeeds] at hn
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hn
  have hi := len_of_get hEvent
  unfold needsIf at hm
  split_ifs at hm with hCovered
  swap
  · simp at hm
  obtain ⟨_, _, _, hObs⟩ := (hCovered : BulkWaitsFor X .read (g, j) (g, i))
  obtain ⟨_, _, _, _, hiWg0, _, _⟩ := Frame.fired_site hs hX hEvent hState
  have hiWg0 : Wg0.Inv P L g d := hiWg0
  have hSub : d.sub = 0 := by simpa [hWait, Wg0.Site.elems] using hiWg0.subLt
  rcases PTX.Step.BulkWait.observed_source hObs with ⟨a, sp, hIssue⟩ | ⟨s, hc, _⟩
  · exact (no_earlier_store hpre hX hs ht (List.mem_range.mp hj) hi.le
      hWait hSub hState hIssue).elim
  · exact (GlobalWrites.no_copy hX hc).elim

/-- The actual opening bulk wait releases the same thread for its last-store publication. -/
theorem opening_bulk_wait_released (ht : Frame.Tracked (Machine.code P L) X) {g tag : Nat}
    {d : Wg0.D} (hEvent : X.get (g, (X.tr g).length - 1) = some ⟨tag, .bulkWait .read 0⟩)
    (hWait : d.site = .bulkWait)
    (hState : Frame.stateAt (Machine.code P L) X g ((X.tr g).length - 1) = some (some (.wg0 d))) :
    PTX.Step.Released L X g := by
  exact ⟨fun _ _ _ _ => opening_bulk_wait_ready hpre hX hs ht hEvent hWait hState⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
