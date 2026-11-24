-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateOrigins
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantChunkAddress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineTracking

@[expose] public section

/-! # Concrete coordinate loads cannot dismiss the TMA lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem coordinate_bytes_range {g i b : Nat} {d : Wg1Tma.D}
    {e : Event} {k : Fin 16} {j : Fin 4} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j) (hKind : e.kind = .rd a bs) (hb : b < 4) :
    (a.loc.at b).space = .shared ∧ L.sharedBase + 221728 ≤ (a.loc.at b).addr ∧
      (a.loc.at b).addr < L.sharedBase + 222752 := by
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hs g (Frame.lt_of_get hX he)).machine he hd
  obtain ⟨_, _, hk, _, hReadLoc⟩ := IndexCoordinateTrace.read_word hpre hSite hFire
  obtain ⟨rfl, -⟩ := Kind.rd.inj (hKind.symm.trans hk)
  have hk := k.isLt
  have hj := j.isLt
  rw [hReadLoc]
  simp only [Loc.at, Wg1Tma.coordBase, Wg1Tma.coordPos, true_and]
  omega

private theorem coordinate_byte_index_source {source : AsyncCopy.Ref}
    {fp : Acc} {raw : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hWrite : X.MemWrites source fp raw) (hCover : fp.Covers l) (hSpace : l.space = .shared)
    (hLow : L.sharedBase + 221728 ≤ l.addr) (hHigh : l.addr < L.sharedBase + 222752) :
    ∃ h t f z extra high, source = .thread (h, t) ∧
      X.get (h, t) = some f ∧ f.kind = .wr fp raw ∧
      Frame.stateAt (Machine.code P L) X h t = some (some (.index z)) ∧
      z.site = .coord extra high := by
  obtain ⟨h, t, rfl, hOrdinary, hOrigin⟩ :=
    coordinate_byte_origin hpre hX hs hWrite hCover hSpace hLow hHigh
  obtain ⟨tag, hGet⟩ := hOrdinary
  rcases hOrigin with ⟨d, extra, high, hd, hSite⟩ | ⟨j, hj, hDismiss, _⟩
  · exact ⟨h, t, _, d, extra, high, rfl, hGet, rfl, hd, hSite⟩
  · obtain ⟨d, e, he, hd, hn⟩ := hDismiss
    have hLt := Frame.lt_of_get hX hGet
    cases dismissal_is_consumer hpre hX hs he hd hn with
    | wg0 d =>
      obtain ⟨start, hLe, initial, hMask, _, hState⟩ :=
        dismissed_wg0_first_mask_ready hpre hX hs he hd hn
      have hWg := RingRoleGeometry.of_trace hX hLt (hs h hLt).machine hd
      rcases softmax_write_outside_coordinates hpre hX hs hWg hState hMask (hLe.trans hj.le)
          ⟨tag, hGet⟩ with hGlobal | hEnd
      · have hShared := hCover.1.symm.trans hSpace
        rw [hGlobal] at hShared
        cases hShared
      · have hByte := hCover.2.2.2
        omega
    | wg2 d =>
      obtain ⟨start, hLe, initial, hScale, _, hState⟩ :=
        dequant_first_scale_of_dismissal hpre hX hs he hd hn
      have hEnd := dequant_write_below_coordinates hpre hX hs hState hScale
        (hLe.trans hj.le) (show X.Writes (h, t) fp raw from ⟨tag, hGet⟩)
      have hByte := hCover.2.2.2
      omega

/-- **A coordinate load returns its published word.** The bytes it reads come from the index
warp's store of the block's word at the read's position. -/
theorem actual_coordinate_value {g i : Nat} {d : Wg1Tma.D}
    {e : Event} {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j) :
    ∃ a bs, e.kind = .rd a bs ∧
      rebuild 3 bs = .ok (b32 (Wg1Tma.coordAt P L g d.block (Wg1Tma.coordPos k.val j.val))) := by
  apply coordinate_value_of_index_writes hpre hX hs he hd hSite
  intro a bs source fp raw b hKind hb hWrite hCover
  obtain ⟨hSpace, hLow, hHigh⟩ := coordinate_bytes_range hpre hX hs he hd hSite hKind hb
  exact coordinate_byte_index_source hpre hX hs hWrite hCover hSpace hLow hHigh

/-- The TMA warp follows its entire concrete trace. -/
theorem tracked_tma_warp {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    {g : Nat} (hw : warpOf L g = 5) (k : Nat) :
    Frame.stateAt (Machine.code P L) X g k ≠ some none :=
  tracked_wg1_warp hpre hX (fun h hh => (hs h hh).machine) (by omega) k

/-- Actual tensor load issuers always have a followed state, including after dismissals
in other roles. -/
theorem actual_tensor_issue_followed {g i addr : Nat} {e : Event} {sp : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .tensorIssue addr sp) :
    Frame.stateAt (Machine.code P L) X g i ≠ some none := by
  rcases actual_tensor_issue_warp hpre hX hs he hk with hWarp | hWarp
  · exact tracked_nonconsumer_warp hpre hX (fun h hh => (hs h hh).machine) (.inl hWarp) i
  · exact tracked_tma_warp hpre hX hs hWarp i

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
