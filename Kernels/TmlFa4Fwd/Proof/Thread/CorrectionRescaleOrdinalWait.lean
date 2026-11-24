-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Correction

/-- A finished correction lane has an actual rescale rendezvous for each
positive score generation before finalization. -/
theorem rescaleWaitOfCompletedVisit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    {g batch visit : Nat} (stage : Fin 2) (hg : g < l.threads)
    (hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hPos : 0 < visit)
    (hVisit : visit < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    ∃ pos, CorrectionWaits X (g,pos) .rescale stage ∧
      (correctionBefore X (g,pos)).barrier (statsBarrierId l g stage) = visit := by
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  obtain ⟨finish,hTerminal⟩ := correctionStatsWaitOfActiveExit hp hX hWarp.1 hWarp.2
    hWork (exitedOfComplete hX hDone hg) true stage
  obtain ⟨selected,hs,hSL,hSH,hFinish⟩ :=
    terminalWaitOrdinalOfTrips hp hX hWork hUsedK hTerminal
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hEq := (hUnique selected ⟨hs,hSL,hSH⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst selected
  obtain ⟨event,hGet,hAction⟩ := hTerminal
  have hLen := len_of_get hGet
  change finish < (X.tr g).length at hLen
  have hBound : visit < ((X.tr g).take finish).countP (correctionStatsWaitMark stage) := by
    rwa [correctionWaitPrefixCount hp hX stage hLen hWarp,
      ← correctionBarrierOrdinal X (g,finish) (statsBarrierId l g stage),hFinish]
  obtain ⟨pos,hBefore,hBarrier,hOrdinal⟩ := correctionNamedWaitAtOrdinal hp hX stage hLen hBound
  change (correctionBefore X (g,pos)).barrier (statsBarrierId l g stage) = visit at hOrdinal
  obtain ⟨found,hFound,hKind⟩ := hBarrier
  have hMark : found.pc ∈ correctionStatsSites stage := by
    apply (correctionStatsWaitMark_iff stage found).mp
    have hC0 := correctionWaitPrefixCount hp hX stage (g := g) (index := pos)
      (by omega) hWarp
    have hC1 := correctionWaitPrefixCount hp hX stage (g := g) (index := pos+1)
      (by omega) hWarp
    have hIn := countP_take_succ hFound (p := Execution.isBarId (statsBarrierId l g stage))
      (by simp [Execution.isBarId,hKind])
    by_contra hNo
    have hNo' := Bool.eq_false_of_not_eq_true hNo
    have hStay := countP_take_succ_false hFound hNo'
    omega
  have he : X.get (g,pos) = some ⟨found.pc,.bar (statsBarrierId l g stage) (some 64) .sync⟩ := by
    rw [hFound]
    cases found
    congr
  have hCases : found.pc = statsBarrierPc stage true ∨
      found.pc = statsBarrierPc stage false ∨ found.pc = correctionSingleStatsPc stage false := by
    fin_cases stage <;>
      simp [correctionStatsSites,statsBarrierPc,correctionSingleStatsPc] at hMark ⊢
    all_goals tauto
  rcases hCases with hRescale | hOther | hInitial
  · exact ⟨pos,rescaleWaitObservation stage (hRescale ▸ he),hOrdinal⟩
  · have hTerm := terminalWaitObservation stage (hOther ▸ he)
    obtain ⟨b,bb,bLo,bHi,hEq⟩ := terminalWaitOrdinalOfTrips hp hX hWork hUsedK hTerm
    have same := (hUnique b ⟨bb,bLo,bHi⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
    subst b
    omega
  · have hw := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    have hs := stage.isLt
    let pair : Fin 8 := ⟨warpIndex l g % 4+4*stage.val,by omega⟩
    have hId : 3+pair.val = statsBarrierId l g stage := by simp [pair,statsBarrierId]; omega
    have hSources := hId ▸ statsBarrierSources hp hX pair
    have hFirst : CorrectionWaits X (g,pos) .initial stage :=
      initialWaitObservation stage (hInitial ▸ he)
    have hZero : (correctionBefore X (g,pos)).barrier (statsBarrierId l g stage) = 0 :=
      correctionInitialWaitOrdinal hp hX hFirst hSources
    exact (hPos.ne' (hOrdinal.symm.trans hZero)).elim

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
