-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxLseAddress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantTileBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites

@[expose] public section

/-! # Every ordinary global write is within the LSE allocation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem actual_lse_extent {i : EvId} {a : Acc} {bs : List Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hw : X.Writes i a bs) (hSpace : a.loc.space = .global) :
    P.lseBase ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ P.lseBase + lseBytes P := by
  obtain ⟨g, k⟩ := i
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g k = some none
  · obtain ⟨j, hj, role, f, hf, hState, hNext⟩ := prior_dismissal (PTX.len_of_get he).le hFollow
    cases dismissal_is_consumer hpre hX hs hf hState hNext with
    | wg0 d =>
      obtain ⟨start, hLe, first, hMask, _, hFirst⟩ :=
        dismissed_wg0_first_mask_ready hpre hX hs hf hState hNext
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      rcases softmax_actual_write_extent hpre hX hs hRole hFirst hMask (hLe.trans hj.le)
        (show X.Writes (g, k) a bs from ⟨tag, he⟩) with ⟨_, hLse⟩ | ⟨hShared, _⟩ | ⟨hShared, _⟩
      · exact actual_lse_write_extent hpre hX hs hMask hFirst (hLe.trans hj.le) hLse
      · rw [hSpace] at hShared
        cases hShared
      · rw [hSpace] at hShared
        cases hShared
    | wg2 d =>
      have hPc := Frame.event_pc hs hX hf hState
      have hDq : dequantTileRegion f.pc := by
        have hLate := (dequant_dismissal_is_read hpre hX (hs g hg).machine hf hState hNext).2.1
        change f.pc = d.site.pc at hPc
        rw [hPc]
        rcases hLate with ⟨r, k, h⟩ | ⟨r, k, h⟩
        · have hScale : ∀ (r k : Fin 4), dequantTileRegion (Wg2.Site.scale r k).pc :=
            by decide +kernel
          rw [h]
          exact hScale r k
        · have hRaw : ∀ (r : Fin 4) (k : Fin 8), dequantTileRegion (Wg2.Site.raw r k).pc :=
            by decide +kernel
          rw [h]
          exact hRaw r k
      have hLater := later_event_in_control_region dequant_tile_region_closed hX hg hf he hj hDq
      have hSmall := GlobalWrites.global_write_candidate hX he rfl hSpace
      change 2667 ≤ tag at hLater
      change tag < 1842 at hSmall
      omega
  · obtain ⟨d, _, _, hLoc, hSize, _⟩ :=
      GlobalWrites.lse_write_at_followed (i := (g, k)) hpre hs hX hFollow ⟨tag, he⟩ hSpace
    rw [hLoc, hSize]
    exact lse_loc_extent hpre (Wg1Mma.eOf_lt_b hpre) (Wg1Mma.queryOf_lt hpre hg)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
