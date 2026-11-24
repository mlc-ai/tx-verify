-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingQkExitHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace

@[expose] public section

/-! # Every output staging write follows all QK acquires of its lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol Protocol.GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}

/-- The QK acquires in a softmax lane's prefix cover all CTA blocks. -/
structure StageQkHistory (P : Params) (L : Launch) (X : Execution) (g i : Nat) : Prop where
  softmax : wgOf L g = 0
  counts : ∀ slot : Fin 2, (Wg0.blocksOf P L g + (1 - slot.val)) / 2 ≤
    okPolls (Object.qkDone.loc L (ctaOf L g) slot) ((X.tr g).take i)

/-- The actual stage prefix includes the last-block PV acquire and all QK acquires before it. -/
structure EpiloguePvHistory (P : Params) (L : Launch) (X : Execution) (g i : Nat) : Prop where
  softmax : wgOf L g = 0
  acquired :
    let block := Wg0.blocksOf P L g - 1
    ∃ w < i, ∃ tag sc, X.get (g, w) = some
      ⟨tag, .wait (Object.svDone.loc L (ctaOf L g) (rawSlot block))
        (block / 2 % 2) true true sc⟩ ∧
      ∀ slot : Fin 2, (Wg0.blocksOf P L g + (1 - slot.val)) / 2 ≤
        okPolls (Object.qkDone.loc L (ctaOf L g) slot) ((X.tr g).take w)

private theorem epilogue_pv_history_from_anchor {start : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hWg : wgOf L g = 0) (hAnchor : FirstMaskAnchor P L X g start)
    (hStart : start ≤ i) (he : X.get (g, i) = some e) (hTag : 1184 < e.pc) :
    EpiloguePvHistory P L X g i := by
  refine ⟨hWg, ?_⟩
  obtain ⟨d, hMask, hFirst, hState⟩ := hAnchor
  obtain ⟨w, hw, hBefore, sc, hGet⟩ :=
    actual_pv_acquire_before_output hpre hX hs he hStart hTag hMask hState
  exact ⟨w, hw, 1184, sc, hGet, fun slot =>
    actual_qk_count_in_epilogue slot hpre hX hs ⟨d, hMask, hFirst, hState⟩
      hBefore hGet (by change 1122 < 1184; decide)⟩

/-- A followed output staging event is in the epilogue after the last QK round. -/
theorem followed_stage_pv_history {d : Wg0.D} {tile : Fin 4} {chunk : Fin 8} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .oStage tile chunk) : EpiloguePvHistory P L X g i := by
  have hg := Frame.lt_of_get hX he
  have hp := Frame.event_pc hs hX he hd
  change e.pc = d.site.pc at hp
  have hTag : 1184 < e.pc := by
    rw [hp, hSite]
    fin_cases tile <;> fin_cases chunk <;> decide
  obtain ⟨start, hStart, hAnchor⟩ :=
    first_mask_of_followed_stage (PTX.len_of_get he).le hd hSite
  exact epilogue_pv_history_from_anchor hpre hX hs
    (RingRoleGeometry.of_trace hX hg (hs g hg).machine hd) hAnchor hStart he hTag

/-- After dismissal, a store covering a shared byte below the raw buffers is an output
staging write. The recorded loop still establishes every earlier QK acquire. -/
theorem dismissed_stage_pv_history {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.Writes (g, i) a bytes) (hCover : a.Covers l) (hSpace : l.space = .shared)
    (hHi : l.addr < L.sharedBase + 131072)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) :
    l.cta = ctaOf L g ∧ L.sharedBase + 65536 ≤ l.addr ∧ EpiloguePvHistory P L X g i := by
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  obtain ⟨start, hStart, d, hSite, hFirst, hState⟩ :=
    mask_anchor_after_dismissal hpre hX hs he hDismiss
  have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  rcases softmax_actual_write_extent hpre hX hs hWg hState hSite hStart ⟨tag, he⟩ with
    ⟨hGlobal, _⟩ | ⟨_, hLo, _, hCta, site, hTag, hGet⟩ | ⟨_, hBase, _⟩
  · have h := hCover.1.symm.trans hSpace
    rw [hGlobal] at h
    cases h
  · refine ⟨hCover.2.1.trans hCta, hLo.trans hCover.2.2.1, ?_⟩
    exact epilogue_pv_history_from_anchor hpre hX hs hWg ⟨d, hSite, hFirst, hState⟩
      hStart hGet hTag
  · have h := hCover.2.2.1
    omega

/-- A concrete deallocation occurs after the releasing lane's final PV acquire. -/
theorem actual_dealloc_pv_history {tag base n : Nat} {group : CtaGroup}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    EpiloguePvHistory P L X g i := by
  obtain ⟨j, hj, _, start, hStart, hAnchor⟩ := actual_softmax_before_dealloc hpre hX hs he
  obtain ⟨d, hMask, hFirst, hState⟩ := hAnchor
  have hg := Frame.lt_of_get hX he
  have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
  have hTag := (ScoreReleaseTrace.resource_source hX he).2 base n rfl
  apply epilogue_pv_history_from_anchor hpre hX hs hWg ⟨d, hMask, hFirst, hState⟩
    (hStart.trans hj.le) he
  change 1184 < tag
  omega

/-- The QK acquires before the PV wait also precede the staging write. -/
theorem EpiloguePvHistory.qk (h : EpiloguePvHistory P L X g i) : StageQkHistory P L X g i := by
  obtain ⟨w, hw, _, _, _, hCounts⟩ := h.acquired
  refine ⟨h.softmax, fun slot => (hCounts slot).trans ?_⟩
  exact (List.take_sublist_take_left hw.le).countP_le

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
