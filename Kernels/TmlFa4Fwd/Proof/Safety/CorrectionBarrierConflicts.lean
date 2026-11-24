-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBarrierOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
import Lemmas.Flow.PollRounds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Flow Thread Epilogue Prologue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem correctionWaitBudget (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    {round : CorrectionRound} {stage : Fin 2} (hWait : CorrectionWaits X (g,j) round stage) :
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      (correctionBefore X (g,j)).barrier (Correction.statsBarrierId l g stage) ≤
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
  have hUsedK := usedKProtected hp hX
  have hWork := Correction.statsWaitHasWork hp hX hWait
  cases round with
  | rescale =>
    exact Correction.rescaleWaitOrdinalWithinTrips hp hX hWork hUsedK hWait
  | terminal =>
    obtain ⟨batch, hb, hLo, hHi, hExact⟩ :=
      Correction.terminalWaitOrdinalOfTrips hp hX hWork hUsedK hWait
    exact ⟨batch, hb, hLo, hHi, hExact.le⟩
  | initial =>
    obtain ⟨batch, ⟨hb, hLo, hHi⟩, _⟩ := tileBatch_existsUnique p hWork
    let w : Fin 8 := ⟨warpIndex l g % 4 + 4 * stage.val, by have := stage.isLt; omega⟩
    have hId : Correction.statsBarrierId l g stage = 3 + w.val := by
      change warpIndex l g % 4 + 3 + 4 * stage.val = 3 + (warpIndex l g % 4 + 4 * stage.val)
      omega
    have hNamed := statsBarrierSources hp hX w
    rw [← hId] at hNamed
    have hOrdinal := correctionInitialWaitOrdinal hp hX hWait hNamed
    refine ⟨batch, hb, hLo, hHi, ?_⟩
    rw [hOrdinal]
    exact Nat.zero_le _

private theorem correctionRoundOrdinal (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {round : CorrectionRound} {stage : Fin 2} (hWait : CorrectionWaits X i round stage)
    {batch : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ i.1 / l.block)
    (hHi : i.1 / l.block < tilePrefix p (batch + 1) * p.heads) :
    let ordinal := (correctionBefore X i).barrier (Correction.statsBarrierId l i.1 stage)
    let trips := Mma.trips p batch (assignedCoordinates p batch (i.1 / l.block)).1
    match round with
    | .initial => ordinal = 0
    | .rescale => 0 < ordinal ∧ ordinal < trips
    | .terminal => ordinal = trips := by
  obtain ⟨g,j⟩ := i
  have hWork := Correction.statsWaitHasWork hp hX hWait
  have hUsedK := usedKProtected hp hX
  obtain ⟨_,_,unique⟩ := tileBatch_existsUnique p hWork
  have same (b : Nat) (h : b < p.batch ∧ tilePrefix p b * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (b + 1) * p.heads) : b = batch :=
    (unique b h).trans (unique batch ⟨hb,hLo,hHi⟩).symm
  cases round with
  | initial =>
    let w : Fin 8 := ⟨warpIndex l g % 4 + 4 * stage.val, by have := stage.isLt; omega⟩
    have hId : Correction.statsBarrierId l g stage = 3 + w.val := by
      change warpIndex l g % 4 + 3 + 4 * stage.val = 3 + (warpIndex l g % 4 + 4 * stage.val)
      omega
    exact correctionInitialWaitOrdinal hp hX hWait (hId.symm ▸ statsBarrierSources hp hX w)
  | rescale =>
    obtain ⟨b,hb',hLo',hHi',hBound⟩ :=
      Correction.rescaleWaitOrdinalBoundsBeforeTerminal hp hX hWork hUsedK hWait
    exact same b ⟨hb',hLo',hHi'⟩ ▸ hBound
  | terminal =>
    obtain ⟨b,hb',hLo',hHi',hExact⟩ :=
      Correction.terminalWaitOrdinalOfTrips hp hX hWork hUsedK hWait
    exact same b ⟨hb',hLo',hHi'⟩ ▸ hExact

/-- The two correction observations at a common barrier ordinal do the same work
in the same stage. The selected tile determines the terminal generation. -/
theorem correctionStatisticsRoundAgrees (hX : Consistent l kernel Assumptions.all m X) {i j : EvId}
    {round round' : CorrectionRound} {stage stage' : Fin 2} (hi : CorrectionWaits X i round stage)
    (hj : CorrectionWaits X j round' stage') (hWarp : SameWarp l i.1 j.1)
    (hOrd : barrierOrdinal X i = barrierOrdinal X j) : round = round' ∧ stage = stage' := by
  have hStage := Fin.ext ((correctionStatsBarrierOrdinal hp hX hi).symm.trans
    ((congrArg (· % 2) hOrd).trans (correctionStatsBarrierOrdinal hp hX hj)))
  subst stage'
  refine ⟨?_, rfl⟩
  have hCta := hWarp.1.2.2
  obtain ⟨batch, ⟨hb,hLo,hHi⟩, _⟩ :=
    tileBatch_existsUnique p (Correction.statsWaitHasWork hp hX hi)
  have hTrips := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).1
  have hI := correctionRoundOrdinal hp hX hi hb hLo hHi
  have hJ := correctionRoundOrdinal hp hX hj hb (hCta ▸ hLo) (hCta ▸ hHi)
  have hRank : (correctionBefore X i).barrier (Correction.statsBarrierId l i.1 stage) =
      (correctionBefore X j).barrier (Correction.statsBarrierId l j.1 stage) := by
    rw [correctionStatsBarrierCount hp hX hi, correctionStatsBarrierCount hp hX hj] at hOrd
    omega
  rw [← hCta] at hJ
  cases round <;> cases round' <;> dsimp only at hI hJ <;> first | rfl | omega

/-- The last statistics wait of the selected tile precedes the final correction arrival.
The same CTA's statistics waits have no later ordinal. -/
theorem correctionStatisticsBeforeFinalOrdinal (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {round : CorrectionRound} {stage : Fin 2} (hWarp : SameWarp l i.1 j.1)
    (hWait : CorrectionWaits X i round stage) (hFinal : FinalAllocationArrival X j .arrive) :
    barrierOrdinal X i < barrierOrdinal X j := by
  obtain ⟨g,i⟩ := i
  obtain ⟨h,j⟩ := j
  have hCta : g / l.block = h / l.block := hWarp.1.2.2
  have hWork := Correction.statsWaitHasWork hp hX hWait
  have hActive : h / l.block < tilePrefix p p.batch * p.heads := hCta ▸ hWork
  have hCorrection := (correctionStatsStageBalance hp hX hWait).1
  have hw : warpIndex l h = warpIndex l g := hWarp.2.symm
  obtain ⟨k, hk, hTerminal⟩ := correctionTerminalStatisticsBeforeFinalArrival hp hX
    (hw.symm ▸ hCorrection.1) (hw.symm ▸ hCorrection.2) hActive hFinal 1
  obtain ⟨batch, hb, hLo, hHi, hBudget⟩ := correctionWaitBudget hp hX hWait
  obtain ⟨batch', hb', hLo', hHi', hExact⟩ :=
    Correction.terminalWaitOrdinalOfTrips hp hX hActive
      (usedKProtected hp hX) hTerminal
  obtain ⟨canonical, _, unique⟩ := tileBatch_existsUnique p hWork
  have hB : batch = batch' :=
    (unique batch ⟨hb,hLo,hHi⟩).trans
      (unique batch' ⟨hb',hCta.symm ▸ hLo',hCta.symm ▸ hHi'⟩).symm
  subst batch'
  rw [← hCta] at hExact
  have hStage := stage.isLt
  have hCount := correctionStatsBarrierCount hp hX hWait
  have hEnd := correctionStatsBarrierCount hp hX hTerminal
  have hLe : barrierOrdinal X (g,i) ≤ barrierOrdinal X (h,k) := by
    rw [hCount, hEnd]
    simp only [Fin.val_one]
    omega
  have hBefore : barrierOrdinal X (h,k) < barrierOrdinal X (h,j) := by
    obtain ⟨event, he, ha⟩ := hTerminal
    have hIs : Execution.isBar event = true := by
      obtain ⟨_, kind⟩ := event
      have hKind := correctionStatsWait hp hX he ha
      change kind = _ at hKind
      subst kind
      rfl
    have hStep := countP_take_succ he hIs
    have hMono := countP_take_mono Execution.isBar (X.tr h) (show k + 1 ≤ j by omega)
    rw [hStep] at hMono
    change ((X.tr h).take k).countP Execution.isBar <
      ((X.tr h).take j).countP Execution.isBar
    omega
  exact hLe.trans_lt hBefore

private theorem correctionStatisticsApartAllocation (hX : Consistent l kernel Assumptions.all m X)
    {g i h j : Nat} {round : CorrectionRound} {stage : Fin 2} (hWarp : SameWarp l g h)
    (hCorrection : 8 ≤ warpIndex l h ∧ warpIndex l h < 12)
    (hStats : CorrectionWaits X (g,i) round stage) {count : Option Nat} {mode : BarMode}
    (hAlloc : BarrierArrival X (h,j) 2 count mode) :
    barrierOrdinal X (g,i) ≠ barrierOrdinal X (h,j) := by
  rcases hAlloc.correctionAllocation hp hX hCorrection with ⟨_, hStart⟩ | ⟨_, hFinal, _⟩
  · have hCount := correctionStatsBarrierCount hp hX hStats
    omega
  · exact Nat.ne_of_lt (correctionStatisticsBeforeFinalOrdinal hp hX hWarp hStats hFinal)

/-- Correction lanes at the same named barrier ordinal always agree on ID and mode. -/
theorem correctionRendezvousAgree (hX : Consistent l kernel Assumptions.all m X) {i j : EvId}
    {id id' : Nat} {count count' : Option Nat} {mode mode' : BarMode} (hWarp : SameWarp l i.1 j.1)
    (hCorrection : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12)
    (he : BarrierArrival X i id count mode) (hf : BarrierArrival X j id' count' mode')
    (hNamed : id ≠ 0) (hNamed' : id' ≠ 0) (hOrdinal : barrierOrdinal X i = barrierOrdinal X j) :
    id = id' ∧ mode = mode' := by
  obtain ⟨g,k⟩ := i
  obtain ⟨h,z⟩ := j
  have hEq : warpIndex l g = warpIndex l h := hWarp.2
  have hCorrection' : 8 ≤ warpIndex l h ∧ warpIndex l h < 12 := hEq ▸ hCorrection
  by_cases hAlloc : id = 2
  · subst id
    by_cases hAlloc' : id' = 2
    · subst id'
      refine ⟨rfl, ?_⟩
      rcases he.correctionAllocation hp hX hCorrection with ⟨hM, hK⟩ | ⟨hM, _, hK⟩ <;>
        rcases hf.correctionAllocation hp hX hCorrection' with ⟨hM', hK'⟩ | ⟨hM', _, hK'⟩
      · exact hM.trans hM'.symm
      · have hOrd : barrierOrdinal X (h,z) = 1 := hOrdinal.symm.trans hK
        exact (Nat.lt_irrefl 1 (hOrd ▸ hK')).elim
      · have hOrd : barrierOrdinal X (g,k) = 1 := hOrdinal.trans hK'
        exact (Nat.lt_irrefl 1 (hOrd ▸ hK)).elim
      · exact hM.trans hM'.symm
    · obtain ⟨_, _, hStats, _, _⟩ := hf.correctionStatistics hp hX hCorrection' hNamed' hAlloc'
      exact (correctionStatisticsApartAllocation hp hX hWarp.symm hCorrection
        hStats he hOrdinal.symm).elim
  · obtain ⟨_, _, hStats, hId, hMode⟩ := he.correctionStatistics hp hX hCorrection hNamed hAlloc
    by_cases hAlloc' : id' = 2
    · subst id'
      exact (correctionStatisticsApartAllocation hp hX hWarp hCorrection'
        hStats hf hOrdinal).elim
    · obtain ⟨_, _, hStats', hId', hMode'⟩ :=
        hf.correctionStatistics hp hX hCorrection' hNamed' hAlloc'
      exact ⟨hId.trans ((correctionStatisticsAgree hp hX hStats hStats' hWarp hOrdinal).trans
        hId'.symm), hMode.trans hMode'.symm⟩

end PTX.Kernels.TmlFa4Fwd.Safety
