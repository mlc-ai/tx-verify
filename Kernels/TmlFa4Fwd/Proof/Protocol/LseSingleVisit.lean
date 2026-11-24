-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LseTerminalSources
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPublication
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitObservedRound
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseAlignment
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics

open PTX PTX.Flow PTX.Proof Epilogue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Thread.Correction

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem lseStatisticsOfSingleVisitWords {store : EvId} {stage : Fin 2}
    {first wait publication batch tile head : Nat} {sumValue maxValue : ℝ} {s : TState}
    {sum maximum : List (Option Byte)} (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hWindow : LseWindowInputs l X store stage first s sum maximum)
    (hPeer : TerminalPeer l X store.1 stage wait publication .final)
    (hTrip : Mma.trips p batch tile = 1)
    (hVisits : SoftmaxSumRun p batch head (stageRow tile stage + rowOf l store.1) 1
      (fun _ => some (abiFloat p.scaleLog2Bits * maxValue)) (fun _ => sumValue))
    (hWords : TerminalPublishedWords l X store.1 stage publication (fl sumValue) (fl maxValue))
    (hScale : s.regs 7134 = some (b32 p.scaleLog2Bits))
    (hSelector : stage = 0 → FirstLseSelector s sum) (hb : batch < p.batch)
    (hr : stageRow tile stage + rowOf l store.1 < p.qLength batch) :
    LseStatisticsAt p batch head (stageRow tile stage + rowOf l store.1) stage s := by
  exact terminalStatisticsOfPublishedWords hp hX hRead hWindow hPeer hVisits
    hTrip.symm (by decide) rfl hWords hScale hSelector hb hr

/-- The single-visit statistics in the correction LSE window follow from the actual
terminal peer and its observed score and Bias operands. -/
theorem lseStatisticsOfObservedSingleVisitPeer (hDone : Complete l X)
    (hFootprint : OutputFootprint p X) {store : EvId} {stage : Fin 2}
    {first wait publication batch tile head : Nat} {s : TState} {sum maximum : List (Option Byte)}
    (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hWindow : LseWindowInputs l X store stage first s sum maximum)
    (hPeer : TerminalPeer l X store.1 stage wait publication .final) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ store.1 / l.block)
    (hHi : store.1 / l.block < tilePrefix p (batch+1) * p.heads)
    (hCoords : assignedCoordinates p batch (store.1 / l.block) = (tile,head))
    (hTrip : Mma.trips p batch tile = 1) (hScale : s.regs 7134 = some (b32 p.scaleLog2Bits))
    (hSelector : stage = 0 → FirstLseSelector s sum)
    (hr : stageRow tile stage + rowOf l store.1 < p.qLength batch) :
    LseStatisticsAt p batch head (stageRow tile stage + rowOf l store.1) stage s := by
  let g := terminalStatsProducer l store.1 stage
  let warp := terminalStatsWarp l store.1 stage
  have hCta : g/l.block = store.1/l.block := terminalStatsCta hp store.1 stage
  have hWarpVal : Prologue.warpIndex l g = warp.val := terminalStatsProducerWarp hp store.1 stage
  have hWarp : Prologue.warpIndex l g < 8 := hWarpVal.symm ▸ warp.isLt
  have hSameWarp : (⟨Prologue.warpIndex l g,hWarp⟩ : Fin 8) = warp := Fin.ext hWarpVal
  have hStage : stageOf warp = stage := by
    apply Fin.ext
    have hRow : rowOf l store.1 < 128 := Nat.mod_lt _ (by decide)
    change (rowOf l store.1 / 32 + 4 * stage.val) / 4 = stage.val
    omega
  have hRow : (g % l.block) % 128 = rowOf l store.1 := by
    have hBound : rowOf l store.1 < 128 := Nat.mod_lt _ (by decide)
    have hStage := stage.isLt
    unfold g terminalStatsProducer
    rw [hp.block]
    omega
  have hCoords' : assignedCoordinates p batch (g/l.block) = (tile,head) :=
    hCta.symm ▸ hCoords
  have hTrip' : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1 := by
    rw [hCoords']
    exact hTrip
  have hProducerRow : 128 * (2 * (assignedCoordinates p batch (g/l.block)).1 +
      (stageOf ⟨Prologue.warpIndex l g,hWarp⟩).val) + (g % l.block) % 128 =
        stageRow tile stage + rowOf l store.1 := by
    rw [hSameWarp,hStage,hRow,hCoords']
    unfold stageRow
    omega
  obtain ⟨maxValue,sumValue,hVisits,hS,hM,hB,hLen⟩ :=
    singleVisitObservedFinalPublication hp hX hDone hFootprint hWarp hb
      (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) hTrip' (hProducerRow.symm ▸ hr)
      hPeer.publication
  have hVisits' : SoftmaxSumRun p batch head (stageRow tile stage + rowOf l store.1) 1
      (fun _ => some (abiFloat p.scaleLog2Bits * maxValue)) (fun _ => sumValue) := by
    rw [hCoords'] at hProducerRow
    simpa only [hCoords',hProducerRow] using hVisits
  rw [hSameWarp] at hS hM hB
  exact lseStatisticsOfSingleVisitWords hp hX hRead hWindow hPeer hTrip hVisits'
    ⟨hS,hM,hB,hLen⟩ hScale hSelector hb hr

/-- An actual LSE window for a single-visit request contains the reference statistics. -/
theorem lseWindowValuesOfSingleVisit (hComplete : Complete l X) (hFootprint : OutputFootprint p X)
    {store : EvId} {stage : Fin 2} {wait first batch : Nat} {state : TState}
    {sum maximum : List (Option Byte)} (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hObserved : LseWindowObservation p l X store stage first state sum maximum)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ store.1 / l.block)
    (hHi : store.1 / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (store.1/l.block)).1 = 1)
    (hRow : stageRow (assignedCoordinates p batch (store.1/l.block)).1 stage +
      rowOf l store.1 < p.qLength batch) :
    let coords := assignedCoordinates p batch (store.1/l.block)
    LseStatisticsAt p batch coords.2 (stageRow coords.1 stage + rowOf l store.1) stage state := by
  obtain ⟨_,_,_,hPeer,_⟩ :=
    terminalStoresOfComplete hp hX (hFootprint.metadataProtected hp).1 hComplete hRead
  exact lseStatisticsOfObservedSingleVisitPeer hp hX hComplete hFootprint hRead hObserved.inputs
    hPeer hb hLo hHi (Prod.eta _).symm hTrip hObserved.scale hObserved.selector hRow

omit hp hX in
/-- The outstanding LSE writes belong to CTAs assigned a repeated-visit tile. -/
def RepeatedLseWriteValues (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∀ (i : EvId) a bytes, X.Writes i a bytes → a.loc.space = .global →
    (∃ batch < p.batch, tilePrefix p batch * p.heads ≤ i.1 / l.block ∧
      i.1 / l.block < tilePrefix p (batch+1)*p.heads ∧
      Mma.trips p batch (assignedCoordinates p batch (i.1/l.block)).1 ≠ 1) →
    LseWriteValue p a bytes

/-- The decoded single-visit writes and the repeated-visit values account for all LSE writes,
also for launches that contain both types of tiles. -/
theorem lseWriteValuesOfRepeatedVisits (hComplete : Complete l X) (hFootprint : OutputFootprint p X)
    (hRepeated : RepeatedLseWriteValues p l X) : LseWriteValues p X := by
  classical
  intro i a bytes hWrite hGlobal
  by_cases hWork : ∃ b < p.batch, tilePrefix p b * p.heads ≤ i.1 / l.block ∧
      i.1 / l.block < tilePrefix p (b+1)*p.heads ∧
      Mma.trips p b (assignedCoordinates p b (i.1/l.block)).1 ≠ 1
  · exact hRepeated i a bytes hWrite hGlobal hWork
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  refine lseWriteValueAtCta hp hX hUsedK
    (observedValidLseStatisticsAtOfReads hp hX ?_) hWrite hGlobal
  intro store stage wait first batch state sum maximum hCta hRead hObserved hb hLo hHi
  dsimp only
  intro hRow
  have hSingle : Mma.trips p batch (assignedCoordinates p batch (store.1/l.block)).1 = 1 := by
    by_contra hNot
    exact hWork ⟨batch,hb,hCta ▸ hLo,hCta ▸ hHi,hCta ▸ hNot⟩
  exact lseWindowValuesOfSingleVisit hp hX hComplete hFootprint hRead hObserved hb hLo hHi
    hSingle hRow

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
