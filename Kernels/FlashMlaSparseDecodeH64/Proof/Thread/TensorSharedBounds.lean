-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.CacheGatherGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawGatherTrace
import Lemmas.Tensor.BoxWrite
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # Shared footprints of the executed tensor loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TensorSharedBounds

open PTX PTX.Flow PTX.AsyncCopy
open MmaDataTrace Result.RawGather

/-- The eight query transfers occupy the first 64 KiB of shared memory. -/
def QueryWindow (L : Launch) (l : Loc) : Prop :=
  L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 65536

/-- The sixteen gathers occupy one of the two consecutive raw buffers. -/
def RawWindow (L : Launch) (l : Loc) : Prop :=
  L.sharedBase + 131072 ≤ l.addr ∧ l.addr < L.sharedBase + 204800

theorem query_raw_disjoint {L : Launch} {l : Loc} (hq : QueryWindow L l) (hr : RawWindow L l) :
    False := by
  unfold QueryWindow RawWindow at *
  omega

private theorem query_write_footprint {P : Params} {L : Launch} {g x y b : Nat} {l : Loc}
    (tile : Fin 8) (hl : TensorCopy.writeLoc (queryTmaSpec P L g tile) x y b = some l) :
    x < 64 ∧ y < 64 ∧ b < 2 ∧
      l = ⟨.shared, ctaOf L g, L.sharedBase + Wg1Mma.qDstOff tile +
        TensorSwizzle.offset .b128 (L.sharedBase + Wg1Mma.qDstOff tile) (128 * y + 2 * x + b)⟩ := by
  obtain ⟨hx, hy, hb⟩ := TensorCopy.writeLoc_bounds hl
  obtain ⟨hCol, hRow, hBytes⟩ := Result.queryTile_shape P L g tile
  rw [hCol] at hx
  rw [hRow] at hy
  rw [hBytes] at hb
  let col : Fin 64 := ⟨x, hx⟩
  let row : Fin 64 := ⟨y, hy⟩
  let byte : Fin 2 := ⟨b, hb⟩
  have hs : TensorTransfer.slotAt (queryTmaSpec P L g tile).descriptor x y b =
      some (Result.queryTileSlot P L g tile col row byte) := by
    unfold TensorTransfer.slotAt
    rw [dite_eq_left (by rwa [hCol]), dite_eq_left (by rwa [hRow]),
      dite_eq_left (by rwa [hBytes])]
    rfl
  rw [TensorCopy.writeLoc, hs, Option.map_some] at hl
  have hp : TensorTile.rowBytes (queryTmaSpec P L g tile).descriptor.box
      (queryTmaSpec P L g tile).descriptor.format.bytes (queryTmaSpec P L g tile).descriptor.swizzle
      = 128 := by
    rw [TensorTile.rowBytes, hCol, hBytes]
    rfl
  have he := Option.some.inj hl
  change (queryTmaSpec P L g tile).toTensorBox.sharedLoc
    (Result.queryTileSlot P L g tile col row byte) = l at he
  unfold TensorBox.sharedLoc TensorTile.sharedByte TensorTile.linearByte at he
  rw [hp] at he
  change Loc.mk .shared (ctaOf L g) _ = l at he
  refine ⟨hx, hy, hb, ?_⟩
  rw [← he]
  congr 1
  let base := L.sharedBase + Wg1Mma.qDstOff tile
  change base + TensorSwizzle.offset .b128 base (y * 128 + x * 2 + b) =
    base + TensorSwizzle.offset .b128 base (128 * y + 2 * x + b)
  rw [show y * 128 + x * 2 + b = 128 * y + 2 * x + b by omega]

/-- A query tile writes only its CTA's query window. -/
theorem query_write_loc {P : Params} {L : Launch} {g x y b : Nat} {l : Loc}
    (tile : Fin 8) (hl : TensorCopy.writeLoc (queryTmaSpec P L g tile) x y b = some l) :
    l.space = .shared ∧ l.cta = ctaOf L g ∧ QueryWindow L l := by
  obtain ⟨hx, hy, hb, rfl⟩ := query_write_footprint tile hl
  refine ⟨rfl, rfl, ?_⟩
  have hOff := TensorCopy.box_offset_lt (base := L.sharedBase + Wg1Mma.qDstOff tile) hx hy hb
  have hTile := tile.isLt
  change L.sharedBase ≤ L.sharedBase + Wg1Mma.qDstOff tile + _ ∧
    L.sharedBase + Wg1Mma.qDstOff tile + _ < L.sharedBase + 65536
  unfold Wg1Mma.qDstOff at *
  omega

/-- Undoing the SW128 layout of a query write recovers its tile, row, column and byte. -/
theorem query_linear_address {P : Params} {L : Launch} {mem0 : Mem0} {g x y b : Nat} {l : Loc}
    (hpre : Pre P L mem0) (tile : Fin 8)
    (hl : TensorCopy.writeLoc (queryTmaSpec P L g tile) x y b = some l) :
    x < 64 ∧ y < 64 ∧ b < 2 ∧ TensorSwizzle.offset .b128 0 l.addr =
      L.sharedBase + 8192 * tile.val + 128 * y + 2 * x + b := by
  obtain ⟨hx, hy, hb, rfl⟩ := query_write_footprint tile hl
  let base := L.sharedBase + Wg1Mma.qDstOff tile
  let index := 128 * y + 2 * x + b
  have hBase : L.sharedBase % 1024 = 0 := hpre.sharedBase ▸ hpre.sharedAlignment
  have hAlign : base % 128 = 0 := by dsimp [base, Wg1Mma.qDstOff]; omega
  refine ⟨hx, hy, hb, ?_⟩
  change TensorSwizzle.offset .b128 0 (base + TensorSwizzle.offset .b128 base index) = _
  rw [← TensorSwizzle.offset_add_base .b128 base index hAlign, TensorSwizzle.offset_involutive]
  dsimp only [base, index, Wg1Mma.qDstOff]
  omega

private theorem gathered_write_loc {L : Launch} {g x y b : Nat}
    {l : Loc} {s : TensorCopy.Spec} {buf : Fin 2} {tile : Fin 16}
    {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    {oy : Int} {rows : Fin 4 → Int}
    (hBox : s.toTensorBox = box base blocks stride cls s.sharedBase oy rows)
    (hDst : s.sharedBase =
      ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.issueDst buf.val tile.val⟩)
    (hl : TensorCopy.writeLoc s x y b = some l) :
    l.space = .shared ∧ l.cta = ctaOf L g ∧ RawWindow L l := by
  have hshape :
      let d := (encodeKv base blocks stride cls).fourRows
      TensorTile.count d.box 0 = 144 ∧ TensorTile.rows d.box = 4 ∧ d.format.bytes = 4 := by
    norm_num [encodeKv, TensorDescriptor.Descriptor.fourRows, TensorTile.count, TensorTile.step,
      TensorTile.rows, TensorTile.rowsOf, Fin.cases, TensorDescriptor.Format.bytes]
  have hBounds := TensorCopy.writeLoc_bounds hl
  change x < TensorTile.count s.toTensorBox.descriptor.box 0 ∧
    y < TensorTile.rows s.toTensorBox.descriptor.box ∧ b < s.toTensorBox.descriptor.format.bytes
    at hBounds
  rw [hBox] at hBounds
  change x < TensorTile.count (encodeKv base blocks stride cls).fourRows.box 0 ∧
    y < TensorTile.rows (encodeKv base blocks stride cls).fourRows.box ∧
    b < (encodeKv base blocks stride cls).fourRows.format.bytes at hBounds
  obtain ⟨hCol, hRow, hBytes⟩ := hshape
  obtain ⟨hx, hy, hb⟩ : x < 144 ∧ y < 4 ∧ b < 4 := by
    rwa [hCol, hRow, hBytes] at hBounds
  change ((TensorTransfer.slotAt s.toTensorBox.descriptor x y b).map s.toTensorBox.sharedLoc) =
    some l at hl
  rw [hBox] at hl
  let col : Fin 144 := ⟨x, hx⟩
  let row : Fin 4 := ⟨y, hy⟩
  let byte : Fin 4 := ⟨b, hb⟩
  have hSlot := Result.RawGather.slotAt base blocks stride cls row col byte
  change TensorTransfer.slotAt (box base blocks stride cls s.sharedBase oy rows).descriptor x y b =
    some (slot base blocks stride cls row col byte) at hSlot
  rw [hSlot] at hl
  change some ((box base blocks stride cls s.sharedBase oy rows).sharedLoc
    (slot base blocks stride cls row col byte)) = some l at hl
  rw [sharedLoc] at hl
  have he := Option.some.inj hl
  rw [← he, hDst]
  refine ⟨rfl, rfl, ?_⟩
  have hb0 := buf.isLt
  have ht := tile.isLt
  unfold RawWindow Wg1Tma.issueDst Wg1Tma.rawBase Loc.at
  change L.sharedBase + 131072 ≤ L.sharedBase + (131072 + 36864 * buf.val + 2304 * tile.val) +
    (576 * y + 4 * x + b) ∧ L.sharedBase + (131072 + 36864 * buf.val + 2304 * tile.val) +
      (576 * y + 4 * x + b) < L.sharedBase + 204800
  omega

private theorem query_spec_of_fire {P : Params} {L : Launch} {mem0 : Mem0} {g address : Nat}
    {d : Wg1Mma.D} {tile : Fin 8} {e : Event} {o : Option TState} {s : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hSite : d.site = .qLoad tile)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e o)
    (he : e.kind = .tensorIssue address s) :
    s = queryTmaSpec P L g tile := by
  obtain ⟨site, block⟩ := d
  change site = _ at hSite
  subst site
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Wg1Mma.code P L g).AtD ⟨.qLoad tile, block⟩ t at hat
  have hPc : t.pc = (Wg1Mma.Site.qLoad tile).pc := hat.1
  change Fires t.pc (match kernel.code[(Wg1Mma.Site.qLoad tile).pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hPc] at hf
  cases hc : kernel.code[(Wg1Mma.Site.qLoad tile).pc]? with
  | none =>
    rw [hc] at hf
    have hk := congrArg Event.kind hf.1
    rw [he] at hk
    cases hk
  | some ins =>
    rw [hc] at hf
    cases o with
    | none =>
      rcases fires_none_ends hf with ⟨f, hf'⟩ | hf' <;> rw [he] at hf' <;> cases hf'
    | some u =>
      have hk := (fires_qLoad hpre hg block tile hat hc hf).1
      exact (Kind.tensorIssue.inj (he.symm.trans hk)).2

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A gather whose issuing state is followed has an exact raw window and completion object. -/
theorem followed_gather_write_loc {g i addr x y byte : Nat} {e : Event} {s : TensorCopy.Spec}
    {l : Loc} {t : Wg1Tma.D} {tile : Fin 16} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hk : e.kind = .tensorIssue addr s)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.tma t)))
    (hd : t.site = .issue tile) (hl : TensorCopy.writeLoc s x y byte = some l) :
    l.space = .shared ∧ l.cta = ctaOf L g ∧ RawWindow L l ∧
      s.mbar = ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff (t.block % 2)⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hState
  obtain ⟨_, hDst, hMbar, _⟩ := TmaGatherCounts.gather_event_fields hpre hd hf hk
  obtain ⟨_, _, rows, hfirst, hcoord, hdesc⟩ :=
    RawGatherTrace.gather_operands hpre hs hX hState hd he hk
  let buf : Fin 2 := ⟨t.block % 2, Nat.mod_lt _ (by decide)⟩
  have hRead {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
      (hdesc : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨1, (encodeKv base blocks stride cls).fourRows⟩) :
      l.space = .shared ∧ l.cta = ctaOf L g ∧ RawWindow L l := by
    obtain ⟨oy, hbox⟩ := canonicalBox (s := s.toTensorBox) hdesc hfirst hcoord
    exact gathered_write_loc (buf := buf) (tile := tile) hbox hDst hl
  obtain ⟨hSpace, hCta, hRange⟩ := hdesc.elim hRead (fun h => hRead h.2)
  exact ⟨hSpace, hCta, hRange, hMbar⟩

/-- Every tracked tensor load writes either its query window or its raw gather window. -/
theorem write_loc_windows_at_followed {g i address x y byte : Nat} {s : TensorCopy.Spec} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hFollowed : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (hi : X.TensorIssue (g, i) address s) (hl : TensorCopy.writeLoc s x y byte = some l) :
    l.space = .shared ∧ l.cta = ctaOf L g ∧
      (QueryWindow L l ∧ s.mbar = ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ ∨
        RawWindow L l ∧ ∃ block, s.mbar =
          ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff (block % 2)⟩) := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, o, hState, hf⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine hFollowed he (by simp)
  have hSite := RingTensorEvents.issue_site hf rfl
  cases d
  case mma d =>
    obtain ⟨tile, hd⟩ := hSite
    have hEq := query_spec_of_fire hpre hg hd hf rfl
    subst s
    obtain ⟨hSpace, hCta, hRange⟩ := query_write_loc tile hl
    exact ⟨hSpace, hCta, .inl ⟨hRange, rfl⟩⟩
  case tma t =>
    obtain ⟨tile, hd⟩ := hSite
    obtain ⟨hSpace, hCta, hRange, hMbar⟩ :=
      followed_gather_write_loc hpre hX hs he rfl hState hd hl
    exact ⟨hSpace, hCta, .inr ⟨hRange, t.block, hMbar⟩⟩
  all_goals exact hSite.elim

/-- The tensor load byte's shared window in a fully followed execution. -/
theorem write_loc_windows {g i address x y byte : Nat} {s : TensorCopy.Spec} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorIssue (g, i) address s) (hl : TensorCopy.writeLoc s x y byte = some l) :
    l.space = .shared ∧ l.cta = ctaOf L g ∧
      (QueryWindow L l ∧ s.mbar = ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ ∨
        RawWindow L l ∧ ∃ block, s.mbar =
          ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff (block % 2)⟩) :=
  write_loc_windows_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX hi.choose_spec)) hi hl

/-- The covered byte of an actual tensor load is in one of the two disjoint shared windows. -/
theorem written_byte_windows_at_followed {i : EvId} {x y byte : Nat} {a : Acc} {bs : List Byte}
    {l : Loc} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hw : X.MemWrites (.async i (.write (.load x y byte))) a bs) (ha : a.Covers l)
    (ht : Frame.stateAt (Machine.code P L) X i.1 i.2 ≠ some none) :
    l.space = .shared ∧ l.cta = ctaOf L i.1 ∧
      (QueryWindow L l ∨ RawWindow L l) ∧ l.addr < L.sharedBase + 222752 := by
  obtain ⟨o, address, value, _, hi, hl, _, hsize, _⟩ := hw
  have hLoc : l = a.loc := by
    obtain ⟨hSpace, hCta, hLo, hHi⟩ := ha
    have hAddr : l.addr = a.loc.addr := by omega
    cases l
    cases hA : a.loc
    simp_all
  obtain ⟨hSpace, hCta, hWindow⟩ := write_loc_windows_at_followed hpre hX hs ht hi hl
  subst l
  refine ⟨hSpace, hCta, ?_⟩
  rcases hWindow with ⟨hq, _⟩ | ⟨hr, _⟩
  · exact ⟨.inl hq, by have h := hq.2; omega⟩
  · exact ⟨.inr hr, by have h := hr.2; omega⟩

/-- The covered byte of an actual tensor load is in one of the two disjoint shared windows. -/
theorem written_byte_windows {i : EvId} {x y byte : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hw : X.MemWrites (.async i (.write (.load x y byte))) a bs) (ha : a.Covers l) :
    l.space = .shared ∧ l.cta = ctaOf L i.1 ∧
      (QueryWindow L l ∨ RawWindow L l) ∧ l.addr < L.sharedBase + 222752 := by
  have hFollow : Frame.stateAt (Machine.code P L) X i.1 i.2 ≠ some none := by
    obtain ⟨_, _, _, _, hi, _, _, _, _⟩ := hw
    exact ht _ _ (Frame.lt_of_get hX hi.choose_spec)
  exact written_byte_windows_at_followed hpre hX hs hw ha hFollow

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TensorSharedBounds
