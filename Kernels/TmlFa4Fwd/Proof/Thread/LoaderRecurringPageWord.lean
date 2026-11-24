-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundPageIndex
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import Kernels.TmlFa4Fwd.Proof.LoaderSteadyRoundPageWords
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- A page-table lookup during a warm or steady traversal of the loader. -/
@[no_expose] def LoaderRecurringPageRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  ∃ site : Fin 2, X.get i = some ⟨(recurringPageReadSite site).pc, .rd a bytes⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hX hFrame

private theorem warmReadWord {g lane j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hl : lane < 32) (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {a : Acc}
    {bytes : List (Option Byte)} (he : X.get (warpLane l g lane, j) = some ⟨946, .rd a bytes⟩) :
    ∃ batch < p.batch, ∃ row < p.kLength batch,
      a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4} := by
  obtain ⟨batch, hb, hLo, hHi, iteration, hi, hRank, pos, hPos, s, ending, hs, hr, hStart⟩ :=
    actualWarmEventCheckpoint hp hX hg hw hl
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hCTA he
      (show 917 ≤ 946 ∧ 946 < 1348 by decide) (by intro _ h; cases h)
  let co := assignedCoordinates p batch (g / l.block)
  let trips := Mma.trips p batch co.1
  let tid := warpLane l g lane % l.block
  let tile := trips - 2 - iteration
  have hTrips := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hTrips
  have hLen := (hp.lengths batch hb).2.2
  have hBound : 128 * (trips - 2) + 127 < 2 ^ 31 := by omega
  have hTile : 128 * tile + 127 < 2 ^ 31 := by unfold tile; omega
  have hi' : iteration ≤ trips - 2 := by
    change iteration < min (trips - 1) 9 at hi
    have := hi.trans_le (Nat.min_le_left _ _)
    omega
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hRow : primingLaneRow tile tid + 64 < 2 ^ 31 := by
    simp only [primingLaneRow, kvCopyColumn, Bool.false_eq_true, ite_false, Nat.add_zero]
    omega
  obtain ⟨u, hu, hU⟩ := warmPageIndexAtRound hi' hBound hTid hs
  have hRun := hr.after_local_nonempty hu (traceAfterObservedEvent he hPos)
  have hRankEq : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
      ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl := by
    have hTail : loaderShuffleTail 1348 946 = 64 := by decide +kernel
    rw [hStart]
    change ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl +
      loaderShuffleTail 1348 946 = _ at hRank
    omega
  refine ⟨batch, hb, ?_⟩
  exact warmPageWordOfRankedRead hp hX hFrame hb hTile hTid hRow hU hRun he hPos hRankEq

private theorem steadyReadWord {g lane j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hl : lane < 32) (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {a : Acc}
    {bytes : List (Option Byte)} (he : X.get (warpLane l g lane, j) = some ⟨1416, .rd a bytes⟩) :
    ∃ batch < p.batch, ∃ row < p.kLength batch,
      a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4} := by
  obtain ⟨batch, hb, hLo, hHi, _, iteration, _, hi, hRank, pos, hPos, s, ending, hs, hr, hStart⟩ :=
    actualSteadyEventCheckpoint hp hX hg hw hl
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hCTA he
      (show 1396 ≤ 1416 ∧ 1416 < 1741 by decide) (by intro _ h; cases h)
  let co := assignedCoordinates p batch (g / l.block)
  let trips := Mma.trips p batch co.1
  let tid := warpLane l g lane % l.block
  let tile := trips - 2 - iteration
  have hTrips := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hTrips
  have hLen := (hp.lengths batch hb).2.2
  have hBound : 128 * (trips - 2) + 127 < 2 ^ 31 := by omega
  have hi' : iteration ≤ trips - 2 := by
    change iteration < trips - 1 at hi
    omega
  have hRow : primingLaneRow tile tid + 64 < 2 ^ 31 := by
    have hTile : 128 * tile + 127 < 2 ^ 31 := by unfold tile; omega
    simp only [primingLaneRow, kvCopyColumn, Bool.false_eq_true, ite_false, Nat.add_zero]
    omega
  obtain ⟨u, hu, hU⟩ := steadyPageIndexAtRound hi' hBound hs
  have hRun := hr.after_local_nonempty hu (traceAfterObservedEvent he hPos)
  have hRankEq : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
      ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl := by
    have hTail : loaderShuffleTail 1741 1416 = 64 := by decide +kernel
    rw [hStart]
    change ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl +
      loaderShuffleTail 1741 1416 = _ at hRank
    omega
  exact ⟨batch, hb, steadyPageWordOfRankedRead hp hX hFrame hb hRow hU hRun he hPos hRankEq⟩

/-- An observed warm or steady page lookup addresses a live page of its selected request. -/
theorem LoaderRecurringPageRead.word {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (h : LoaderRecurringPageRead X i a bytes) :
    ∃ batch < p.batch, ∃ page < (p.kLength batch + 15) / 16,
      a = {loc := globalLoc (pageWordAddress p batch page), size := 4} := by
  obtain ⟨g, j⟩ := i
  obtain ⟨site, he⟩ := h
  let pc := (recurringPageReadSite site).pc
  have hLow : 297 < pc := by fin_cases site <;> decide
  have hHigh : pc < 1862 := by fin_cases site <;> decide
  have hSite : pc ∉ registerHintSites := by fin_cases site <;> decide
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < pc by omega) hSite
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) pc at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hCuQ := hp.cuQ_protected (fun w a data loc => Thread.Loader.loaderOutputWrites hFrame
    (w := w) (a := a) (data := data) (loc := loc))
  have hWork := loaderOwnPrefixEventRequiresActiveTile hp hX hw hCuQ he hLow hHigh
  have hGet : X.get (warpLane l g lane, j) = some ⟨pc, .rd a bytes⟩ := hLane.symm ▸ he
  have hRow : ∃ batch < p.batch, ∃ row < p.kLength batch,
      a = {loc := globalLoc (pageWordAddress p batch (row / 16)), size := 4} := by
    fin_cases site
    · exact warmReadWord hp hX hFrame hg hw hl hWork hGet
    · exact steadyReadWord hp hX hFrame hg hw hl hWork hGet
  obtain ⟨batch, hb, row, hr, eq⟩ := hRow
  exact ⟨batch, hb, row / 16, by omega, eq⟩

end PTX.Kernels.TmlFa4Fwd.Thread
