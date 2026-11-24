-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.GlobalConflicts
import Kernels.TmlFa4Fwd.Proof.Thread.LseCoordinates
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Epilogue

private theorem coordinatesInjective {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {batch cta other : Nat}
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hLo' : tilePrefix p batch * p.heads ≤ other)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads)
    (hHi' : other < tilePrefix p (batch + 1) * p.heads)
    (hEq : assignedCoordinates p batch cta = assignedCoordinates p batch other) : cta = other := by
  let tiles := requestTiles p batch
  let width := sectionWidth tiles p.heads
  let base := tilePrefix p batch * p.heads
  have hWidth : 0 < width :=
    sectionWidth_pos (Nat.zero_lt_of_lt (assignedCoordinates_valid hp hLo hHi).2)
  have bounded (g : Nat) (hMin : base ≤ g) (h : g < tilePrefix p (batch + 1) * p.heads) :
      g - base < tiles * p.heads := by
    rw [tilePrefix_succ, Nat.add_mul] at h
    dsimp [base, tiles] at hMin ⊢
    omega
  have ha := (sectionItem_coords hWidth (bounded cta hLo hHi)).2.2
  have hb := (sectionItem_coords hWidth (bounded other hLo' hHi')).2.2
  change sectionItem tiles p.heads width (assignedCoordinates p batch cta).1
    (assignedCoordinates p batch cta).2 = cta - base at ha
  change sectionItem tiles p.heads width (assignedCoordinates p batch other).1
    (assignedCoordinates p batch other).2 = other - base at hb
  rw [hEq, hb] at ha
  dsimp [base] at ha
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Two actual LSE stores with a common byte belong to the same correction lane. -/
theorem sameLseWordSameLane (hFrame : OutputIntentFootprint p X) {i j : EvId} {a b : Acc}
    {bytes data : List Byte} {loc : Loc} (hi : X.Writes i a bytes) (hj : X.Writes j b data)
    (ha : a.Covers loc) (hb : b.Covers loc) (hGlobal : loc.space = .global) : i.1 = j.1 := by
  have hCuQ := (outputIntent_iff_cuQProtected hp hX).mp hFrame
  have hFoot := globalWriteFootprintsMatch hp hX hFrame (e := .thread i) (f := .thread j)
    hi.access hj.access ha hb hGlobal
  obtain ⟨hA, hWarp⟩ := Thread.Correction.lseStoreAssigned hp hX hi (ha.1.symm.trans hGlobal)
  obtain ⟨hB, hWarp'⟩ := Thread.Correction.lseStoreAssigned hp hX hj (hb.1.symm.trans hGlobal)
  obtain ⟨batch, hBatch, stage, hLo, hHi, hRow, hLoc, _⟩ := hA
  obtain ⟨batch', hBatch', stage', hLo', hHi', hRow', hLoc', _⟩ := hB
  have hLocEq := hLoc.symm.trans (hFoot.1.trans hLoc')
  have hRowEq := congrArg (·.at 0) hLocEq
  obtain ⟨hPacked, hHead, _⟩ := lseByte_inj (hp.packedRow_lt hBatch hRow)
    (hp.packedRow_lt hBatch' hRow') hp.lseStride (by decide : 0 < 4) (by decide : 0 < 4) hRowEq
  obtain ⟨rfl, hWithin⟩ := hp.packedRow_inj hBatch hBatch' hRow hRow' hPacked
  have hiRow : Correction.rowOf l i.1 < 128 := Nat.mod_lt _ (by decide)
  have hjRow : Correction.rowOf l j.1 < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  have hStage' := stage'.isLt
  dsimp [stageRow] at hWithin
  have hTile : (assignedCoordinates p batch (i.1 / l.block)).1 =
      (assignedCoordinates p batch (j.1 / l.block)).1 := by omega
  have hRowSame : Correction.rowOf l i.1 = Correction.rowOf l j.1 := by omega
  have hCta := coordinatesInjective hp hLo hLo' hHi hHi' (Prod.ext hTile hHead)
  change 8 ≤ i.1 % l.block / 32 ∧ i.1 % l.block / 32 < 12 at hWarp
  change 8 ≤ j.1 % l.block / 32 ∧ j.1 % l.block / 32 < 12 at hWarp'
  change (i.1 % l.block) % 128 = (j.1 % l.block) % 128 at hRowSame
  have hLane : i.1 % l.block = j.1 % l.block := by omega
  rw [← Nat.mod_add_div i.1 l.block, ← Nat.mod_add_div j.1 l.block, hLane, hCta]

/-- Overlapping ordinary LSE stores are ordered by their correction lane's program order. -/
theorem lseWritesOrdered (hFrame : OutputIntentFootprint p X) {i j : EvId} {a b : Acc}
    {bytes data : List Byte} {loc : Loc} (hi : X.Writes i a bytes) (hj : X.Writes j b data)
    (ha : a.Covers loc) (hb : b.Covers loc) (hGlobal : loc.space = .global) (hNe : i ≠ j) :
    ByteCausality l X loc (.thread i) (.thread j) ∨
      ByteCausality l X loc (.thread j) (.thread i) := by
  have hLane := sameLseWordSameLane hp hX hFrame hi hj ha hb hGlobal
  have hDistinct : i.2 ≠ j.2 := fun h => hNe (Prod.ext hLane h)
  rcases Nat.lt_or_gt_of_ne hDistinct with h | h
  · exact .inl (.direct (.inl (.single (.inl
      (po_of_overlap hi.access hj.access hLane h ⟨loc, ha, hb⟩)))))
  · exact .inr (.direct (.inl (.single (.inl
      (po_of_overlap hj.access hi.access hLane.symm h ⟨loc, hb, ha⟩)))))

/-- Unordered global writers of one byte are both output tensor stores of a single CTA. -/
theorem unorderedGlobalWriters (hFrame : OutputIntentFootprint p X) {e f : AsyncCopy.Ref}
    {a b : Acc} {loc : Loc} (he : X.Intent e a true) (hf : X.Intent f b true) (ha : a.Covers loc)
    (hb : b.Covers loc) (hGlobal : loc.space = .global) (hNe : e ≠ f)
    (hef : ¬ ByteCausality l X loc e f) (hfe : ¬ ByteCausality l X loc f e) :
    ∃ i j x y k x' y' k', e = .async i (.write (.store x y k)) ∧
      f = .async j (.write (.store x' y' k')) ∧ i.1 / l.block = j.1 / l.block := by
  have hCuQ := (outputIntent_iff_cuQProtected hp hX).mp hFrame
  have hFoot := globalWriteFootprintsMatch hp hX hFrame he hf ha hb hGlobal
  have ga := ha.1.symm.trans hGlobal
  have gb := hb.1.symm.trans hGlobal
  rcases Thread.globalWriteSource hX he ga with
    ⟨i, bs, rfl, hI⟩ | ⟨i, x, y, k, addr, sa, rfl, hI, hA, haSize⟩
  · rcases Thread.globalWriteSource hX hf gb with
      ⟨j, cs, rfl, hJ⟩ | ⟨j, _, _, _, _, _, rfl, _, _, hbSize⟩
    · have hDiff : i ≠ j := fun h => hNe (congrArg AsyncCopy.Ref.thread h)
      exact ((lseWritesOrdered hp hX hFrame hI hJ ha hb hGlobal hDiff).elim hef hfe).elim
    · obtain ⟨_, _, _, _, _, haSize⟩ := Thread.lseWriteShape hp hX hI ga
      have hWidth := hFoot.2
      omega
  · rcases Thread.globalWriteSource hX hf gb with
      ⟨j, cs, rfl, hJ⟩ | ⟨j, x', y', k', addr', sb, rfl, hJ, hB, hbSize⟩
    · obtain ⟨_, _, _, _, _, hbSize⟩ := Thread.lseWriteShape hp hX hJ gb
      have hWidth := hFoot.2
      omega
    · have hDst := hA.trans (congrArg some (Acc.loc_of_one ha haSize))
      have hDst' := hB.trans (congrArg some (Acc.loc_of_one hb hbSize))
      exact ⟨i, j, x, y, k, x', y', k', rfl, rfl,
        Protocol.Output.sameOutputByteSameCta hp hX hI hJ hDst hDst'⟩

end PTX.Kernels.TmlFa4Fwd.Safety
