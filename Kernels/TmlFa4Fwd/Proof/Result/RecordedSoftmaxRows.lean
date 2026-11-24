-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Result.RepeatedOutputHistory
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecordedSoftmaxRowPrefix
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalRowPublication
public import Kernels.TmlFa4Fwd.Proof.Protocol.LseSingleVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.ReachedTerminalSoftmaxRow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX PTX.Proof Epilogue Prologue Protocol Thread Thread.Correction
open TmlFa4Fwd.Correction (terminalStatsProducer terminalStatsProducerWarp terminalStatsWarp rowOf)
open _root_.PTX.Kernels.TmlFa4Fwd.Mma (trips)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Each completed live softmax row has its exact ordered visits and the
terminal values from that same actual lane. -/
def CompletedSoftmaxRows (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∀ producer < l.threads, ∀ stage : Fin 2, warpIndex l producer / 4 = stage.val →
    ∀ batch < p.batch, tilePrefix p batch*p.heads ≤ producer/l.block →
    producer/l.block < tilePrefix p (batch+1)*p.heads →
    let coords := assignedCoordinates p batch (producer/l.block)
    let blocks := trips p batch coords.1
    let row := stageRow coords.1 stage+producer%l.block%128
    row < p.qLength batch → blocks ≠ 1 →
    ∃ refs sums maximum,
      RecordedSoftmaxRowPrefix p l X producer batch coords.2 row stage blocks blocks refs sums ∧
      abiFloat p.scaleLog2Bits*maximum = (refs (blocks-1)).getD 0 ∧
      TerminalLaneValues l X producer (sums (blocks-1)) maximum

/-- Select the producer for one correction row and transport its arithmetic history
to the correction lane's request and stage coordinates. -/
theorem CompletedSoftmaxRows.selected (hp : Pre p l m)
    (hHistory : CompletedSoftmaxRows p l X) {g batch : Nat} (stage : Fin 2)
    (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let coords := assignedCoordinates p batch (g/l.block)
    let blocks := trips p batch coords.1
    let row := stageRow coords.1 stage+rowOf l g
    let producer := terminalStatsProducer l g stage
    blocks ≠ 1 → row < p.qLength batch →
    ∃ refs sums maximum,
      RecordedSoftmaxRowPrefix p l X producer batch coords.2 row stage blocks blocks refs sums ∧
      abiFloat p.scaleLog2Bits*maximum = (refs (blocks-1)).getD 0 ∧
      TerminalDrainValues l X g stage (sums (blocks-1)) maximum := by
  dsimp only
  intro hRepeat hRow
  let producer := terminalStatsProducer l g stage
  have hOwner : producer/l.block = g/l.block := TmlFa4Fwd.Correction.terminalStatsCta hp g stage
  have hProducer : producer < l.threads := by
    rw [show l.threads = l.grid*l.block from rfl,hp.block]
    have hGrid := NamedBar.cta_lt hg
    rw [hp.block] at hOwner hGrid
    have hMod := Nat.mod_lt producer (show 0 < 512 by decide)
    have hSplit := Nat.mod_add_div producer 512
    omega
  have hpStage : warpIndex l producer/4 = stage.val := by
    rw [terminalStatsProducerWarp hp]
    change (rowOf l g/32+4*stage.val)/4 = stage.val
    have hr : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    omega
  have hpRow : producer%l.block%128 = rowOf l g := by
    have hVal := stage.isLt
    have hR : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    unfold producer terminalStatsProducer
    rw [hp.block]
    omega
  obtain ⟨refs,sums,maximum,hPrefix,hMax,hDrain⟩ :=
    hHistory producer hProducer stage hpStage batch hb (hOwner.symm ▸ hLo)
      (hOwner.symm ▸ hHi) (by rwa [hOwner,hpRow]) (by rwa [hOwner])
  rw [hOwner,hpRow] at hPrefix
  have hTerminal := hDrain.forCorrection (g := g) (stage := stage) rfl
  rw [hOwner] at hTerminal
  rw [hOwner] at hMax
  exact ⟨refs,sums,maximum,hPrefix,hMax,hTerminal⟩

/-- Normalize the real PV outputs of all repeated visits using the paired
producer's recorded softmax probabilities and terminal statistics. -/
theorem repeatedOutputValuesOfRecordedSoftmaxRows
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hHistory : CompletedSoftmaxRows p l X) :
    RepeatedOutputValues p X := by
  apply repeatedOutputValuesOfSoftmaxVisits hp hX hDone hFootprint
  intro g hg _ _ stage batch hb
  dsimp only
  intro hLo hHi hRepeat hRow
  have hWork : g/l.block < tilePrefix p p.batch*p.heads := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨refs,sums,maximum,hPrefix,_,hTerminal⟩ :=
    hHistory.selected hp stage hg hb hLo hHi hRepeat hRow
  refine SoftmaxRowVisits.ofRecorded hX stage refs sums hPrefix.recurrence
    hPrefix.probabilities hPrefix.factors ?_
  intro pos hWait hPass
  obtain ⟨pub,hWords,hGeneration⟩ :=
    Protocol.Statistics.terminalWordsOfCompletedDrainForWait hp hX hDone
      (hFootprint X hX) hWork hTerminal hWait hPass
  exact ⟨pub,maximum,hWords,hGeneration⟩

/-- LSE and O consume the terminal statistics of the same recorded row history. -/
theorem repeatedLseWriteValuesOfRecordedSoftmaxRows
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    (hHistory : CompletedSoftmaxRows p l X) :
    Protocol.Statistics.RepeatedLseWriteValues p l X := by
  intro i a bytes hWrite hGlobal
  rintro ⟨expected,hBatch,hFirst,hLast,hRepeat⟩
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  refine TmlFa4Fwd.Correction.lseWriteValueAtCta hp hX hUsedK
    (observedValidLseStatisticsAtOfReads hp hX ?_) hWrite hGlobal
  intro store stage wait first batch state sum maximum hCta hRead hObserved hb hLo hHi
  dsimp only
  intro hRow
  have hWork : i.1/l.block < tilePrefix p p.batch*p.heads := hLast.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show expected+1 ≤ p.batch by omega)))
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hSame := (hUnique batch ⟨hb,hCta ▸ hLo,hCta ▸ hHi⟩).trans
    (hUnique expected ⟨hBatch,hFirst,hLast⟩).symm
  subst expected
  have hRepeat' : trips p batch (assignedCoordinates p batch (store.1/l.block)).1 ≠ 1 :=
    hCta.symm ▸ hRepeat
  have hThread : store.1 < l.threads := by
    obtain ⟨_,hGet,_⟩ := hRead.terminal
    exact event_thread_lt (e := (store.1,wait)) hX hGet
  obtain ⟨refs,sums,mx,hPrefix,hReference,hDrain⟩ :=
    hHistory.selected hp stage hThread hb hLo hHi hRepeat' hRow
  obtain ⟨pub,_,_,hPeer,_⟩ :=
    Protocol.Statistics.terminalStoresOfComplete hp hX hCuQ hDone hRead
  have hProd : terminalStatsProducer l store.1 stage < l.threads := by
    obtain ⟨_,hGet,_⟩ := hPeer.publication
    exact event_thread_lt hX hGet
  have hWords := hDrain.publishedWords hp hX hPeer.publication (exitedOfComplete hX hDone hProd)
  have hBlocks := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).1
  exact Protocol.Statistics.terminalStatisticsOfPublishedWords hp hX hRead hObserved.inputs hPeer
    hPrefix.recurrence rfl hBlocks hReference hWords hObserved.scale hObserved.selector hb hRow

end
end PTX.Kernels.TmlFa4Fwd.Result
