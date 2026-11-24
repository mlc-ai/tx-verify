-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity

@[expose] public section

/-! # Actual ordinary writers in the query tile -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

set_option maxHeartbeats 600000 in
/-- Any ordinary write to the query tile comes from a followed dequantization thread. -/
theorem actual_query_tile_writer {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {a : Acc} {word : List Byte} {byte : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.Writes (g, i) a word) (ha : a.Covers byte) (hsp : byte.space = .shared)
    (hQ : TensorSharedBounds.QueryWindow L byte) :
    byte.cta = ctaOf L g ∧
      ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) ∧ d.site = .store r s := by
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  have hHi : byte.addr < L.sharedBase + 65536 := hQ.2
  have hn : Frame.stateAt (Machine.code P L) X g i ≠ some none := by
    intro hDismiss
    obtain ⟨start, hLe, d, hSite, _, hState⟩ :=
      mask_anchor_after_dismissal hpre hX hs he hDismiss
    have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
    rcases softmax_actual_write_extent hpre hX hs hWg hState hSite hLe ⟨tag, he⟩ with
      ⟨hGlobal, _⟩ | ⟨_, hBase, _⟩ | ⟨_, hBase, _⟩
    · have h := ha.1.symm.trans hsp
      rw [hGlobal] at h
      cases h
    · have h := ha.2.2.1
      omega
    · have h := ha.2.2.1
      omega
  obtain ⟨d, _, hState, _⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine hn he (by simp)
  have hRegions := RawSharedWrites.ordinary_window_regions_of_state (i := (g, i))
    hpre hX hs hState ⟨tag, he⟩ ha
  rcases hRegions with
    hGlobal | ⟨_, _, hRegions, _⟩
  · rw [hsp] at hGlobal
    cases hGlobal
  rcases hRegions with ⟨_, hc, hDequant⟩ | ⟨hStage, _⟩ | hHigh
  · exact ⟨hc, hDequant⟩
  · omega
  · omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
