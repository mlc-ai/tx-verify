-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingMaskOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantChunkAddress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTensorCoordinateExclusion

@[expose] public section

/-! # The concrete writers of the validity ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Any actual writer of a validity byte is a one-byte store from its index quad leader. -/
theorem actual_validity_source {w : Ref} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.MemWrites w a bs) (hCover : a.Covers l) (hSpace : l.space = .shared)
    (hLow : L.sharedBase + 221696 ≤ l.addr) (hHigh : l.addr < L.sharedBase + 221728) :
    ∃ (g i : Nat) (e : Event) (d : Wg1Index.D) (extra : Bool) (quad : Fin 8),
      w = .thread (g, i) ∧ X.get (g, i) = some e ∧ e.kind = .wr a bs ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.index d)) ∧
      d.site = .valid extra ∧ Wg1Index.Inv P L g d ∧ laneOf L g = 4 * quad.val ∧
      a.loc = l ∧ l = ⟨.shared, ctaOf L g, L.sharedBase + 221696 + 8 * d.phase + quad.val⟩ ∧
      a.size = 1 ∧ bs = (Value.bits 8
        (BitVec.ofNat 64 (Wg1Index.quadByte P L g d.block (4 * quad.val)))).toBytes := by
  rcases Wg2.raw_read_competing_kinds hX hw hCover hSpace with
    ⟨⟨g, i⟩, rfl, hOrdinary⟩ | ⟨⟨g, i⟩, x, y, b, rfl⟩
  · obtain ⟨tag, he⟩ := hOrdinary
    have hg := Frame.lt_of_get hX he
    rcases Frame.fired hs hX he with ⟨s, _, hState, _⟩ | ⟨_, _, _, hFault⟩
    · cases s with
      | some s =>
        obtain ⟨d, extra, quad, hd, hSite, hInv, hLane, ha, hl, hSize, hBytes⟩ :=
          StageWriteClasses.validity_from_followed_write (i := (g, i))
            hpre hX hs hState ⟨tag, he⟩ hCover hSpace hLow hHigh
        exact ⟨g, i, _, d, extra, quad, rfl, he, rfl, hd, hSite, hInv, hLane, ha, hl, hSize, hBytes⟩
      | none =>
        obtain ⟨j, hj, role, f, hf, hd, hn⟩ := prior_dismissal (PTX.len_of_get he).le hState
        cases dismissal_is_consumer hpre hX hs hf hd hn with
        | wg0 d =>
          obtain ⟨start, hLe, initial, hMask, _, hFirst⟩ :=
            dismissed_wg0_first_mask_ready hpre hX hs hf hd hn
          have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
          rcases softmax_write_outside_coordinates hpre hX hs hWg hFirst hMask (hLe.trans hj.le)
              (show X.Writes (g, i) a bs from ⟨tag, he⟩) with hGlobal | hEnd
          · have hShared := hCover.1.symm.trans hSpace
            rw [hGlobal] at hShared
            cases hShared
          · have hByte := hCover.2.2.2
            omega
        | wg2 d =>
          obtain ⟨start, hLe, initial, hScale, _, hFirst⟩ :=
            dequant_first_scale_of_dismissal hpre hX hs hf hd hn
          have hEnd := dequant_write_below_coordinates hpre hX hs hFirst hScale
            (hLe.trans hj.le) (show X.Writes (g, i) a bs from ⟨tag, he⟩)
          have hByte := hCover.2.2.2
          omega
    · cases hFault
  · exact (no_tensor_write_above_raw_buffers hpre hX hs hw hCover (by omega)).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
