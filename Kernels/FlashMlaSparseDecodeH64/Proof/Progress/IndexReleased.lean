-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.IndexReuseBlocker
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.IndexShuffle
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MemoryConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingArrivalRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIndexArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIndexInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIndexWrite

public section

/-! # Progress for all pending index warp sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- Every pending index lane in a maximal followed execution leads to an earlier pending lane. -/
theorem pending_index_earlier {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Index.D} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g (.index d)) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.index d) := by
  have hX := hmax.1
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hUb : ¬ HasUb X := fun h => hSafe (.inl h)
  have hRel := ClosingArrival.index_released_of_tail hp.2
  have hInput (hSite : IndexInput d.site) : False :=
    hmax.not_grows (index_input_extension hpre hs hX hUb hp.1 hRel hp.2 hSite)
  have hWrite (hSite : (∃ extra high, d.site = .coord extra high) ∨
      ∃ extra, d.site = .valid extra) : False :=
    hmax.not_grows (index_write_extension hpre hs hX ht hUb hp.1 hRel hp.2 hSite)
  cases hSite : d.site
  case lenOrig => exact (hInput (hSite.symm ▸ .lenOrig)).elim
  case lenExtra => exact (hInput (hSite.symm ▸ .lenExtra)).elim
  case pair extra first high => exact (hInput (hSite.symm ▸ .pair extra first high)).elim
  case waitFree extra =>
    exact pending_index_free_earlier hpre hmax hs ht hUb hp hRel (.producer hSite)
  case quad1 extra =>
    exact pending_index_shuffle_earlier (second := false) hpre hmax hs ht hUb hp hSite
  case quad2 extra =>
    exact pending_index_shuffle_earlier (second := true) hpre hmax hs ht hUb hp hSite
  case coord extra high => exact (hWrite (.inl ⟨extra, high, hSite⟩)).elim
  case valid extra => exact (hWrite (.inr ⟨extra, hSite⟩)).elim
  case ready extra =>
    have hRmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ →
        a.release = false :=
      fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim
    exact (hmax.not_grows (index_arrival_extension hpre hs hX
      (Safety.reads_ordered hpre hX hs ht) (sync_guarded hX hSafe)
      (fun _ _ _ _ he => write_no_release hX he) hRmw (no_thread_fence hX)
      hUb hp.1 hRel hp.2 hSite)).elim
  case barrier =>
    exact (closing_arrival_not_pending hpre hmax hs hUb hp.1 hRel hp.2 hSite).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
