-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.DequantPvWait
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.RawReadyWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryProducerBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MemoryConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressDequantControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressDequantRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressRingArrival

public section

/-! # Progress for all released dequantization lane sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- A pending, released dequantization lane in a maximal followed execution has an earlier
pending dependency. The remaining sites can extend the actual trace. -/
theorem pending_dequant_released {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg2.D} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g (.wg2 d)) (hRel : PTX.Step.Released L X g) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.wg2 d) := by
  have hX := hmax.1
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hub : ¬ HasUb X := fun h => hSafe (.inl h)
  let hSg := sync_guarded hX hSafe
  let hOrd := Safety.reads_ordered hpre hX hs ht
  have hPublish (hSite : RingArrival (.wg2 d)) : False :=
    hmax.not_grows (ring_arrival_extension hpre hs hX hOrd hSg
      (fun _ _ _ _ he => write_no_release hX he)
      (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
      (no_thread_fence hX) hub hp.1 hRel hp.2 hSite)
  cases hSite : d.site
  case lenOrig =>
    exact (hmax.not_grows
      (dequant_length_extension (orig := true) hpre hs hX hub hp.1 hRel hp.2 hSite)).elim
  case lenExtra =>
    exact (hmax.not_grows
      (dequant_length_extension (orig := false) hpre hs hX hub hp.1 hRel hp.2 hSite)).elim
  case qUtccp =>
    exact earlier_query_producer_of_pending hpre hmax hs ht hSg hp hRel (.dequant d rfl hSite)
  case rawReady => exact pending_raw_ready_earlier hpre hmax hs ht hub hp hRel hSite
  case svDone =>
    obtain ⟨h, q, _, hPend, hLt⟩ := pending_dequant_pv_earlier hpre hmax hs ht hSg hp hRel hSite
    exact ⟨h, q, hPend, hLt⟩
  case scale row word =>
    exact (hmax.not_grows (dequant_read_extension (which := .scale row word)
      hpre hs hX hSafe hp.1 hRel hp.2 hSite)).elim
  case raw row word =>
    exact (hmax.not_grows (dequant_read_extension (which := .raw row word)
      hpre hs hX hSafe hp.1 hRel hp.2 hSite)).elim
  case store row word =>
    exact (hmax.not_grows (dequant_store_extension hpre hs hX hub ht hp.1 hRel hp.2 hSite)).elim
  case fence =>
    exact (hmax.not_grows (dequant_fence_extension hs hX hOrd hSafe hp.1 hRel hp.2 hSite)).elim
  case ready => exact (hPublish (.dequantReady hSite)).elim
  case free => exact (hPublish (.rawFree hSite)).elim
  case barrier =>
    exact (closing_arrival_not_pending hpre hmax hs hub hp.1 hRel hp.2 hSite).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
