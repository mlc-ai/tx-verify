-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTensorCoordinateExclusion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateIndex

@[expose] public section

/-! # Classify actual writes covering packed coordinate storage -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An ordinary covering write is a followed index store, unless the concrete writer has
already passed a dismissal in a softmax or dequantization lane. -/
theorem coordinate_write_origin {g i : Nat} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.Writes (g, i) a bytes) (hCover : a.Covers l) (hShared : l.space = .shared)
    (hLow : L.sharedBase + 221728 ≤ l.addr) (hHigh : l.addr < L.sharedBase + 222752) :
    (∃ d extra high, Frame.stateAt (Machine.code P L) X g i = some (some (.index d)) ∧
      d.site = .coord extra high) ∨
    (∃ j < i, Dismisses P L X (g, j) ∧ (wgOf L g = 0 ∨ wgOf L g = 2)) := by
  have he : X.get (g, i) = some ⟨hw.choose, .wr a bytes⟩ := hw.choose_spec
  let tag := hw.choose
  have hg := Frame.lt_of_get hX he
  rcases Frame.fired hs hX he with ⟨state, _, hState, _⟩ | ⟨_, _, _, hUb⟩
  · cases state with
    | some state =>
      obtain ⟨d, extra, high, hd, hSite, _⟩ :=
        StageWriteClasses.coordinate_from_followed_write (i := (g, i)) hpre hX hs hState
          hw hCover hShared hLow hHigh
      exact .inl ⟨d, extra, high, hd, hSite⟩
    | none =>
      obtain ⟨j, hj, hdismiss⟩ := prior_dismissal (PTX.len_of_get he).le hState
      obtain ⟨d, e, hearly, hd, hn⟩ := hdismiss
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      have hKind : (⟨tag, .wr a bytes⟩ : Event).kind = .wr a bytes := rfl
      cases dismissal_is_consumer hpre hX hs hearly hd hn with
      | wg0 d => exact .inr ⟨j, hj, ⟨_, _, hearly, hd, hn⟩, .inl hRole⟩
      | wg2 d => exact .inr ⟨j, hj, ⟨_, _, hearly, hd, hn⟩, .inr hRole⟩
  · cases hUb

/-- Every actual source of a packed coordinate byte is an ordinary write. A followed
source is an index store, leaving only dismissed softmax or dequantization to check. -/
theorem coordinate_byte_origin {w : AsyncCopy.Ref} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.MemWrites w a bytes) (hCover : a.Covers l) (hShared : l.space = .shared)
    (hLow : L.sharedBase + 221728 ≤ l.addr) (hHigh : l.addr < L.sharedBase + 222752) :
    ∃ g i, w = .thread (g, i) ∧ X.Writes (g, i) a bytes ∧
      ((∃ d extra high, Frame.stateAt (Machine.code P L) X g i = some (some (.index d)) ∧
        d.site = .coord extra high) ∨
      (∃ j < i, Dismisses P L X (g, j) ∧ (wgOf L g = 0 ∨ wgOf L g = 2))) := by
  rcases Wg2.raw_read_competing_kinds hX hw hCover hShared with
    ⟨⟨g, i⟩, rfl, hOrdinary⟩ | ⟨⟨g, i⟩, x, y, b, rfl⟩
  · exact ⟨g, i, rfl, hOrdinary,
      coordinate_write_origin hpre hX hs hOrdinary hCover hShared hLow hHigh⟩
  · exact (no_tensor_write_above_raw_buffers hpre hX hs hw hCover (by omega)).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
