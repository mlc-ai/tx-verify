-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitFinalizationValues
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStage
import Kernels.TmlFa4Fwd.Proof.Protocol.LseTerminalSources
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalPublishedWords
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof Prologue Epilogue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Mma (trips)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFootprint : OutputFootprint p X) {g pos batch : Nat} (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRow : stageRow (assignedCoordinates p batch (g/l.block)).1 stage + rowOf l g <
      p.qLength batch)
include hp hX hDone hFootprint stage hb hLo hHi hTrip hRow

private theorem singleVisitStatsAtTerminalWait (hTerm : CorrectionWaits X (g,pos) .terminal stage)
    (hPass : pos+1 < (X.tr g).length) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row := stageRow coords.1 stage + rowOf l g
    ∃ (pub : Nat) (sum maximum : ℝ),
      firstReference p batch coords.2 row 1 = abiFloat p.scaleLog2Bits * maximum ∧
      SoftmaxSumRun p batch coords.2 row 1 (fun _ => some (abiFloat p.scaleLog2Bits * maximum))
        (fun _ => sum) ∧
      TerminalPublishedWords l X g stage pub (fl sum) (fl maximum) ∧
      TerminalGeneration l X g stage (pub-2) pos := by
  let coords := assignedCoordinates p batch (g/l.block)
  let row := stageRow coords.1 stage + rowOf l g
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  have hCta : producer/l.block = g/l.block := terminalStatsCta hp g stage
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hRecord := hTerm
  obtain ⟨_,he,_⟩ := hRecord
  have hGrid : g/l.block < l.grid := NamedBar.cta_lt (event_thread_lt hX he)
  have hProducer : producer < l.threads := by
    change producer < l.grid*l.block
    have hLocal : producer % l.block < l.block := Nat.mod_lt _ (by rw [hp.block]; decide)
    have hIndex := Nat.mod_add_div producer l.block
    rw [hCta] at hIndex
    have hNext := Nat.mul_le_mul_left l.block (show g/l.block+1 ≤ l.grid by omega)
    rw [Nat.mul_add,Nat.mul_one] at hNext
    rw [Nat.mul_comm l.grid l.block]
    omega
  have hWarpVal : warpIndex l producer = warp.val := terminalStatsProducerWarp hp g stage
  have hWarp : warpIndex l producer < 8 := hWarpVal.symm ▸ warp.isLt
  have hSameWarp : (⟨warpIndex l producer,hWarp⟩ : Fin 8) = warp := Fin.ext hWarpVal
  have hStage : stageOf warp = stage := by
    apply Fin.ext
    have hLimit : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    change (rowOf l g/32+4*stage.val)/4 = stage.val
    omega
  have hLocal : producer%l.block%128 = rowOf l g := by
    have hLimit : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hS := stage.isLt
    unfold producer terminalStatsProducer
    rw [hp.block]
    omega
  have hProducerRow : 128 * (2 * (assignedCoordinates p batch (producer/l.block)).1 +
        (stageOf ⟨warpIndex l producer,hWarp⟩).val) + producer%l.block%128 = row := by
    rw [hCta,hSameWarp,hStage,hLocal]
    unfold row stageRow coords
    omega
  obtain ⟨pub,hPeer,_⟩ := Protocol.Statistics.terminalFinalPeerOfActiveWait hp hX
    (hFootprint.metadataProtected hp).1 (hFootprint.metadataProtected hp).2 hWork hTerm hPass
    (exitedOfComplete hX hDone hProducer)
  obtain ⟨maximum,sum,hVisits,hRef,hSum,hMax,hPub,hLen⟩ :=
    singleVisitObservedFinalPublicationWithReference hp hX hDone hFootprint hWarp hb
      (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip) (hProducerRow.symm ▸ hRow)
      hPeer.publication
  rw [hSameWarp] at hSum hMax hPub
  have hWords : TerminalPublishedWords l X g stage pub (fl sum) (fl maximum) :=
    ⟨hSum,hMax,hPub,hLen⟩
  obtain ⟨origin,hOrigin,hGeneration,_⟩ := Protocol.Statistics.terminalStoresOfFinalPeer hX hPeer
  have hSource : pub-2 = origin := by omega
  have hGeneration : TerminalGeneration l X g stage (pub-2) pos := hSource.symm ▸ hGeneration
  rw [hProducerRow,hCta] at hRef hVisits
  exact ⟨pub,sum,maximum,hRef,hVisits,hWords,hGeneration⟩


/-- From the actual final statistics cursor, correction reads the matched sum and
numerator, then normalizes and publishes the selected single-visit row. -/
theorem singleVisitNormalizedStage {t : TState} {F : List (Nat × Value)}
    (ht : At t (statsBarrierPc stage false) F)
    (hFrame : ∀ sum maximum, FinalStageFrame l g stage sum maximum F)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    let coords := assignedCoordinates p batch (g/l.block)
    let row := stageRow coords.1 stage + rowOf l g
    let old := fun (c : Fin 16) (k : Nat) => (2 : ℝ) ^ (-firstReference p batch coords.2 row 1) *
      maskedBlockSum (p.keyCount batch row) 1 0 (weightedValue p batch coords.2 row (8*c.val+k))
    ∃ (sum maximum : ℝ) (start : Nat) (u : TState), pos+6 ≤ start ∧
      NormalizedOutput l X g start stage old (normalizingReciprocal sum) ∧
      (∀ (c : Fin 16) (k : Fin 8), old c k.val * normalizingReciprocal sum =
        attention p batch coords.2 row (8*c.val+k.val)) ∧
      At u (outputFencePc stage+3) (finalStageLoadFacts l stage sum maximum F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+163)) none := by
  let coords := assignedCoordinates p batch (g/l.block)
  let row := stageRow coords.1 stage + rowOf l g
  let reference := firstReference p batch coords.2 row 1
  let old := fun (c : Fin 16) (k : Nat) => (2 : ℝ) ^ (-reference) *
    maskedBlockSum (p.keyCount batch row) 1 0 (weightedValue p batch coords.2 row (8*c.val+k))
  have hBarrier := holds_mem ht.2.2.2.2 (hFrame 0 0).barrier
  obtain ⟨he,_,hTail⟩ := observeStatsBarrier hp stage false ht hBarrier hRun
  have hTerm := terminalWaitObservation stage he
  have hPass : pos+1 < (X.tr g).length := by
    by_contra! h
    rw [List.drop_eq_nil_iff.mpr h] at hTail
    cases hTail
  obtain ⟨pub,sum,maximum,hRef,hVisits,hWords,hGeneration⟩ :=
    singleVisitStatsAtTerminalWait hp hX hDone hFootprint stage hb hLo hHi hTrip hRow hTerm hPass
  have hInputs : FinalStageInputs l X g pos stage sum maximum old := by
    constructor
    · intro bs he
      exact hWords.read hp hX hTerm rfl rfl hGeneration 0 ⟨_,he⟩
    · intro bs he
      exact hWords.read hp hX hTerm rfl rfl hGeneration 1 ⟨_,he⟩
    · intro n k _ _ chunk vals he
      have hValues := singleVisitFinalizationLoadValues hp hX hDone hFootprint
        (batch := batch) stage chunk (load := (g,pos+4+n+1+k+1+10*chunk.val))
        he hb hLo hHi hTrip hRow
      exact hValues
  obtain ⟨start,u,hStart,hOutput,hu,hU⟩ := observeFinalStage hp stage sum maximum old
    ht (hFrame sum maximum) hInputs hRun
  have hRef' : reference = abiFloat p.scaleLog2Bits * maximum := hRef
  have hSumRun : SoftmaxSumRun p batch coords.2 row 1 (fun _ => some reference) (fun _ => sum) :=
    by simpa only [← hRef'] using hVisits
  let acc := fun (_ : Nat) d => (2 : ℝ) ^ (-reference) *
    maskedBlockSum (p.keyCount batch row) 1 0 (weightedValue p batch coords.2 row d)
  have hAttention : SoftmaxRun p batch coords.2 row 1 (fun _ => some reference) (fun _ => sum)
      acc := ⟨hSumRun,fun _ _ => rfl,fun _ hi => by omega⟩
  have hCover : p.keyCount batch row ≤ 128 * 1 := by
    have hRowTile : row < 256*(coords.1+1) := by
      have hRowBound : rowOf l g < 128 := Nat.mod_lt _ (by decide)
      have hS := stage.isLt
      unfold row stageRow
      omega
    have h := p.keyCount_le_kvBlocks (b := batch) hRowTile
    change p.keyCount batch row ≤ 128 * trips p batch coords.1 at h
    exact hTrip ▸ h
  refine ⟨sum,maximum,start,u,hStart,hOutput,?_,hu,hU⟩
  intro chunk k
  have hd : 8*chunk.val+k.val < 128 := by have := chunk.isLt; have := k.isLt; omega
  exact (hAttention.result (by decide) (hp.keyCount_pos hb hRow) hCover hd).1

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
