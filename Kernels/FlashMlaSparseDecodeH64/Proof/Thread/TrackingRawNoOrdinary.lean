-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantChunkAddress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites

@[expose] public section

/-! # Ordinary writes cannot reach the raw ring in a concrete trace -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

set_option maxHeartbeats 1000000 in
/-- Only a tensor write can supply a byte of a raw buffer, even after another lane dismisses. -/
theorem no_actual_ordinary_raw_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.Writes (g, i) a bytes)
    (hCover : a.Covers l) (hSpace : l.space = .shared)
    (hLow : L.sharedBase + 131072 ≤ l.addr) (hHigh : l.addr < L.sharedBase + 204800) : False := by
  obtain ⟨tag, he⟩ := hw
  have hw : X.Writes (g, i) a bytes := ⟨tag, he⟩
  rcases Frame.fired hs hX he with ⟨state, _, hd, _⟩ | ⟨_, _, _, hUb⟩
  · cases state with
    | some state =>
      exact RawSharedWrites.no_ordinary_at_followed (i := (g, i))
        hpre hX hs hd hw hCover hSpace hLow hHigh
    | none =>
      obtain ⟨j, hj, z, f, hf, hz, hn⟩ := prior_dismissal (PTX.len_of_get he).le hd
      have hg := Frame.lt_of_get hX he
      cases dismissal_is_consumer hpre hX hs hf hz hn with
      | wg0 d =>
        obtain ⟨start, hLe, initial, hMask, _, hState⟩ :=
          dismissed_wg0_first_mask_ready hpre hX hs hf hz hn
        have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hz
        rcases softmax_write_extent hpre hX hs hWg hState hMask (hLe.trans hj.le) hw with
          hGlobal | hEnd | ⟨hStart, _⟩
        · exact Space.noConfusion (hGlobal.symm.trans (hCover.1.symm.trans hSpace))
        · have hByte := hCover.2.2.2
          omega
        · have hByte := hCover.2.2.1
          omega
      | wg2 d =>
        obtain ⟨start, hLe, initial, hScale, _, hState⟩ :=
          dequant_first_scale_of_dismissal hpre hX hs hf hz hn
        have hEnd := dequant_write_below_coordinates hpre hX hs hState hScale (hLe.trans hj.le) hw
        have hByte := hCover.2.2.2
        omega
  · cases hUb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
