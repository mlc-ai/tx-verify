-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateAlignment
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTmaReadback

@[expose] public section

/-! # Actual byte sources of the first coordinate load of a slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow
open Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable {g i h t : Nat} {d : Wg1Tma.D} {s : Wg1Index.D} {e f : Event} {k : Fin 16} {j : Fin 4}
    {a fp : Acc} {bs : List (Option Byte)} {raw : List Byte} {offset : Nat} {extra high : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j) (hf : X.get (h, t) = some f)
    (hState : Frame.stateAt (Machine.code P L) X h t = some (some (.index s)))
include hpre hX hs he hd hSite hf hState

/-- A covering coordinate store has the reader's slot, lane and word address. -/
theorem coordinate_source_geometry (hStore : s.site = .coord extra high)
    (hReadKind : e.kind = .rd a bs) (hStoreKind : f.kind = .wr fp raw) (hb : offset < 4)
    (hCover : fp.Covers (a.loc.at offset)) :
    fp.loc = a.loc ∧ ctaOf L g = ctaOf L h ∧ s.block % 4 = d.block % 4 ∧
      laneOf L h = Wg1Tma.coordPos k.val j.val / 2 ∧
      (if high then 1 else 0) = Wg1Tma.coordPos k.val j.val % 2 ∧
      raw = (b32 (Wg1Index.coordValue P L h s.block (laneOf L h)
        (if high then 1 else 0))).toBytes := by
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  obtain ⟨_, hRead⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  obtain ⟨_, hWrite⟩ := RingEvents.fired_of_trace hX (hs h hh).machine hf hState
  obtain ⟨_, _, hKind, _, hReadLoc⟩ := IndexCoordinateTrace.read_word hpre hSite hRead
  obtain ⟨rfl, -⟩ := Kind.rd.inj (hReadKind.symm.trans hKind)
  obtain ⟨hRaw, hWidth, hWriteLoc⟩ :=
    IndexCoordinateTrace.written_word hpre hStore hWrite hStoreKind
  let pos := Wg1Tma.coordPos k.val j.val
  let part : Nat := if high then 1 else 0
  have hPos : pos < 64 := by
    have hk := k.isLt
    have hj := j.isLt
    unfold pos Wg1Tma.coordPos
    omega
  have hLane : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hPart : part < 2 := by cases high <;> decide
  have hAddrRead : a.loc.addr = (L.sharedBase + 221728) + 256 * (d.block % 4) + 4 * pos := by
    rw [hReadLoc]
    simp [Wg1Tma.coordBase, pos, Nat.add_assoc]
  have hAddrWrite : fp.loc.addr = (L.sharedBase + 221728) + 256 * (s.block % 4) +
      8 * laneOf L h + 4 * part := by
    rw [hWriteLoc]
    simp [Wg1Tma.coordBase, part, Nat.add_assoc]
  have hCta := hCover.2.1
  rw [hReadLoc, hWriteLoc] at hCta
  change ctaOf L g = ctaOf L h at hCta
  have hlo := hCover.2.2.1
  have hhi := hCover.2.2.2
  change fp.loc.addr ≤ a.loc.addr + offset at hlo
  change a.loc.addr + offset < fp.loc.addr + fp.size at hhi
  rw [hAddrWrite, hAddrRead] at hlo
  rw [hAddrWrite, hAddrRead, hWidth] at hhi
  obtain ⟨hSlot, hLane', hPart'⟩ :=
    IndexTma.coordinate_address_match hLane hPart hPos hb hlo hhi
  have hLoc : fp.loc = a.loc := by
    rw [hWriteLoc, hReadLoc, ← hCta, hSlot]
    congr 1
    change L.sharedBase + Wg1Tma.coordBase (d.block % 4) + 8 * laneOf L h + 4 * part =
      L.sharedBase + Wg1Tma.coordBase (d.block % 4) + 4 * pos
    omega
  exact ⟨hLoc, hCta, hSlot, hLane', hPart', hRaw⟩

/-- An index store in the same generation and covering a coordinate byte supplies the exact
requested coordinate. The address identifies the slot, lane, and word within that lane. -/
theorem coordinate_bytes_of_same_index_use (hStore : s.site = .coord extra high)
    (hUse : s.block / 4 = d.block / 4) (hReadKind : e.kind = .rd a bs)
    (hStoreKind : f.kind = .wr fp raw) (hb : offset < 4) (hCover : fp.Covers (a.loc.at offset)) :
    fp.loc = a.loc ∧ raw = (b32 (Wg1Tma.coordAt P L g d.block
      (Wg1Tma.coordPos k.val j.val))).toBytes := by
  obtain ⟨hLoc, hCta, hSlot, hLane, hPart, hRaw⟩ :=
    coordinate_source_geometry hpre hX hs he hd hSite hf hState hStore
      hReadKind hStoreKind hb hCover
  have hBlock : s.block = d.block := by omega
  refine ⟨hLoc, ?_⟩
  rw [hRaw, hBlock, hLane, hPart, IndexTma.coord_same_cta hCta.symm,
    ← IndexTma.coordAt_eq_coordValue]
end

/-- A coordinate load returns the published word if its current publication is visible and all
covering sources belong to the same generation or are ordered around that publication. -/
theorem coordinate_value_of_publication {g i : Nat} {d : Wg1Tma.D}
    {e : Event} {k : Fin 16} {j : Fin 4}
    {a aw : Acc} {bs : List (Option Byte)} {w : EvId}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j)
    (hKind : e.kind = .rd a bs) (hSize : a.size = 4)
    (hLoc : a.loc = aw.loc) (hWidth : aw.size = 4)
    (hWrite : X.MemWrites (.thread w) aw
      (b32 (Wg1Tma.coordAt P L g d.block (Wg1Tma.coordPos k.val j.val))).toBytes)
    (hBefore : baseCausality L X w (g, i))
    (hSources :
      ∀ b < 4, ∀ source fp raw,
      X.rf (.thread (g, i)) b = some source → X.MemWrites source fp raw →
      fp.Covers (a.loc.at b) →
      (∃ h t f s extra high, source = .thread (h, t) ∧
        X.get (h, t) = some f ∧ f.kind = .wr fp raw ∧
        Frame.stateAt (Machine.code P L) X h t = some (some (.index s)) ∧
        s.site = .coord extra high ∧ s.block / 4 = d.block / 4) ∨
      ByteCausality L X (a.loc.at b) source (.thread w) ∨
      ByteCausality L X (a.loc.at b) (.thread (g, i)) source) :
    rebuild 3 bs = .ok (b32 (Wg1Tma.coordAt P L g d.block (Wg1Tma.coordPos k.val j.val))) := by
  have hRead : X.MemReads (.thread (g, i)) a bs := by
    obtain ⟨tag, kind⟩ := e
    cases hKind
    exact .inl ⟨tag, he⟩
  exact IndexTma.rebuild_of_publication hX hRead hSize hLoc hWidth hWrite hBefore (by
    intro b hb source fp raw hRf hWr hCover
    rcases hSources b hb source fp raw hRf hWr hCover with
      hUse | hearlier | hlater
    · obtain ⟨h, t, f, s, _, _, _, hf, hfKind, hState, hStore, hSameUse⟩ := hUse
      exact .inl (coordinate_bytes_of_same_index_use hpre hX hs he hd hSite hf hState hStore
        hSameUse hKind hfKind hb hCover)
    · exact .inr (.inl hearlier)
    · exact .inr (.inr hlater))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
