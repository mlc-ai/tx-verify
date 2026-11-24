-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseFallback
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.NoCancellation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Every correction warp with an observed late event and an assigned tile reaches the
active request. This follows the actual first-group or fallback scheduler before the tile body. -/
theorem correctionActiveTileOfEventWithVote {g lane j : Nat} {target : Event} (hg : g < l.threads)
    (hLoWarp : 8 ≤ warpIndex l g) (hHiWarp : warpIndex l g < 12) (hl : lane < 32)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads) (hLate : 7884 < target.pc)
    (he : X.get (warpLane l g lane, j) = some target) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ (ends : Nat → Option TState), ∃ sh,
        ∃ active : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
          sh 1 ends, WarpFollowsEvent l X g active.pos lane j target := by
  have hRouted := correctionFirstRouteOfEvent hp hX hg hLoWarp hHiWarp hl (by omega) he
  by_cases hFirst : g / l.block < tilePrefix p (min p.batch 31) * p.heads
  · rw [ite_eq_left hFirst] at hRouted
    obtain ⟨ends, ready, hReady⟩ := hRouted
    obtain ⟨batch, hBatch, hLo, hHi, chosen, hChosen⟩ :=
      correctionFirstBatchTo hp hX hg hFirst ready (.inr hReady) (by omega)
    have hb := hBatch.trans_le (Nat.min_le_left ..)
    have hGroup : batch < 0 + 31 := hBatch.trans_le (Nat.min_le_right ..)
    obtain ⟨sh, active, hActive⟩ := correctionTileOfChoiceEvent hp hX hg (Nat.zero_le _)
      hGroup hb hLo hHi chosen hLate (hChosen hReady)
    exact ⟨batch, hb, hLo, hHi, ends, sh, active, hActive⟩
  · rw [ite_eq_right hFirst] at hRouted
    obtain ⟨ends, fallback, hFallback⟩ := hRouted
    rcases correctionFallbackGroupEvent hp hX hg fallback (Nat.le_of_not_gt hFirst)
        (by omega) hFallback with
      ⟨hExhausted, _⟩ | ⟨first, batch, hBase, hGroup, hb, hLo, hHi, _, ready, hReady⟩
    · exact (Nat.not_lt_of_ge hExhausted hWork).elim
    · obtain ⟨sh, active, hActive⟩ := correctionTileOfGroupEvent hp hX hg hBase hGroup hb hLo hHi
        ready hLate hReady
      exact ⟨batch, hb, hLo, hHi, ends, sh, active, hActive⟩

theorem correctionActiveTileOfEvent {g lane j : Nat} {target : Event} (hg : g < l.threads)
    (hLoWarp : 8 ≤ warpIndex l g) (hHiWarp : warpIndex l g < 12) (hl : lane < 32)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads) (hLate : 7884 < target.pc)
    (he : X.get (warpLane l g lane, j) = some target) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ (ends : Nat → Option TState), ∃ sh votes,
        ∃ active : SchedulerWarpAt l X g 7932 (correctionActiveTileFacts p l g batch)
          sh votes ends, WarpFollowsEvent l X g active.pos lane j target := by
  obtain ⟨batch,hb,hLo,hHi,ends,sh,active,hActive⟩ := correctionActiveTileOfEventWithVote
    hp hX hg hLoWarp hHiWarp hl hWork hLate he
  exact ⟨batch,hb,hLo,hHi,ends,sh,1,active,hActive⟩

/-- A completed correction lane writes each assigned valid stage row at its decoded LSE site. -/
theorem correctionLaneLseWriter (hComplete : Complete l X) {g lane batch tile head : Nat}
    (hg : g < l.threads) (hLoWarp : 8 ≤ warpIndex l g) (hHiWarp : warpIndex l g < 12)
    (hl : lane < 32)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * i)).at k)) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCoords : assignedCoordinates p batch (g / l.block) = (tile, head)) (stage : Fin 2)
    (hRow : stageRow tile stage + rowOf l (warpLane l g lane) < p.qLength batch) :
    ∃ pos bytes, X.get (warpLane l g lane, pos) = some ⟨lseGuardPc stage + 1, .wr
      {loc := p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l (warpLane l g lane)) head,
        size := 4} bytes⟩ := by
  let thread := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hThread : thread < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  obtain ⟨pc, hExit⟩ := (hComplete.1 thread hThread).resolve_left (noCanceled hX)
  let j := (X.tr thread).length - 1
  rw [List.getLast?_eq_getElem?] at hExit
  have hGetExit : X.get (thread, j) = some ⟨pc, .exit⟩ := hExit
  have hExitPc := actualExitPc hX hGetExit
  subst pc
  have hWork : g / l.block < tilePrefix p p.batch * p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨chosen, hChosen, hBegin, hEnd, ends, sh, votes, active, hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hLoWarp hHiWarp hl hWork (by decide) hGetExit
  obtain ⟨_, _, hUnique⟩ := tileBatch_existsUnique p hWork
  have heq := (hUnique chosen ⟨hChosen, hBegin, hEnd⟩).trans (hUnique batch ⟨hb, hLo, hHi⟩).symm
  subst chosen
  have hRead := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s, rest, visits, hs, hWalk, hLater, consumed, hTrace, _⟩ :=
    correctionLseReadyFromSelected hp hX hb hLo hHi (active.checkpoint lane hl) (hUsedK batch hb)
      hRead hActive.before (by decide) hGetExit
  rw [hCoords] at hs
  have ⟨hTile, hHead⟩ := assignedCoordinates_valid hp hLo hHi
  rw [hCoords] at hTile hHead
  obtain ⟨bytes, hWrite⟩ :=
    correctionLseWriterFromReady hp stage hb hHead hTile hRow hs (by decide) hWalk hLater
  let event : Event := ⟨lseGuardPc stage + 1, .wr
    {loc := p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l thread) head, size := 4}
    bytes⟩
  have hIn : event ∈ (X.tr thread).drop (active.pos lane) := by
    rw [hTrace]
    exact List.mem_append_right consumed hWrite
  obtain ⟨pos, hPos⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_drop hIn)
  exact ⟨pos, bytes, hPos⟩

/-- The CTA assigned to each packed output row has a completed store for every LSE byte. -/
theorem lseHasWriter (hComplete : Complete l X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * i)).at k)) {batch head row k : Nat}
    (hb : batch < p.batch) (hh : head < p.heads) (hr : row < p.qLength batch) (hk : k < 4) :
    ∃ w a bytes, X.MemWrites w a bytes ∧
      a.Covers ((p.lseLoc (p.qOffset batch + row) head).at k) := by
  let cta := workItem p batch (row / 256) head
  let g := cta * l.block + 256 + row % 128
  let stage : Fin 2 := ⟨row / 128 % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨hCta, hBegin, hEnd, hAssigned⟩ := hp.row_workItem hb hr hh
  have hg : g < l.threads := by
    change cta * l.block + 256 + row % 128 < l.grid * l.block
    rw [hp.block]
    omega
  have hCTA : g / l.block = cta := by
    dsimp only [g]
    rw [hp.block]
    omega
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    dsimp only [warpIndex, g]
    rw [hp.block]
    omega
  have hSelf : warpLane l g (laneOf l g) = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hRow : stageRow (row / 256) stage + rowOf l (warpLane l g (laneOf l g)) = row := by
    rw [hSelf]
    dsimp only [stageRow, stage, rowOf, g]
    rw [hp.block]
    omega
  have hCoords : assignedCoordinates p batch (g / l.block) = (row / 256, head) := by
    rw [hCTA]
    exact hAssigned
  obtain ⟨pos, bytes, hWrite⟩ := correctionLaneLseWriter hp hX hComplete hg hWarp.1 hWarp.2 hLane
      hUsedK hb (hCTA.symm ▸ hBegin) (hCTA.symm ▸ hEnd) hCoords
    stage (hRow.symm ▸ hr)
  have hAddr : p.qOffset batch + stageRow (row / 256) stage + rowOf l (warpLane l g (laneOf l g)) =
      p.qOffset batch + row := by rw [Nat.add_assoc, hRow]
  rw [hAddr] at hWrite
  refine ⟨.thread (warpLane l g (laneOf l g), pos), _, bytes, .inl ⟨_, hWrite⟩, ?_⟩
  exact ⟨rfl, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
