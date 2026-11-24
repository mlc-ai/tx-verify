-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbabilityWriteOrder
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitCorrectionWrites
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Lemmas.Tcgen05.TcDataCell

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma Prologue
open Epilogue (assignedCoordinates)

private theorem firstScoreConsumerStage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer commit wait : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait) :
    consumer % l.block / 128 = stage.val := by
  have hAddr := congrArg Loc.addr (firstScoreWaitAddress hp hX hPhase.waitEvent)
  change l.sharedBase + (80 + 8 * stage.val) =
    l.sharedBase + (80 + 8 * (warpIndex l consumer / 4)) at hAddr
  have hStage : warpIndex l consumer / 4 = stage.val := by omega
  simpa only [warpIndex,Nat.div_div_eq_div_mul,show 32*4 = 128 by decide] using hStage

/-- In a single-visit request, every observed store of a score cell is a probability
publication after the lane has completed that score load. The same acquire orders it
after all eight initial MMA fragments. -/
theorem singleVisitScoreStoreOrdering {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {batch : Nat}
    {stage : Fin 2} {producer consumer commit wait read complete : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (producer / l.block)).1 = 1)
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    (hWaitRead : wait < read) (hReadComplete : read < complete)
    (hWaitLd : X.get (consumer,complete) = some ⟨4826,.tc .waitLd⟩)
    (q : Fin 4) (word : Fin 32) {other : EvId}
    (hWrite : StoreCell l X other
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    ReadBefore l X .ld (consumer,read) other ∧
      ∀ issue < commit, X.TcAsync (producer,issue) →
        ReadBefore l X .acc (producer,issue) other := by
  obtain ⟨g,j⟩ := other
  have hRecorded := hWrite
  obtain ⟨a,vals,shape,k,⟨pc,he⟩,_,hCell⟩ := hRecorded
  rcases Thread.tensorStoreSite hX he with ⟨round,quarter,rfl⟩ | ⟨writtenStage,chunk,rfl⟩
  · obtain ⟨w,hw,rfl,hLen,rfl⟩ := Thread.Scores.probabilityStoreAddress hp hX round quarter he
    have hWrittenStage : g % l.block / 128 = (stageOf w).val := by
      change g % l.block / 128 = w.val / 4
      rw [hw]
      simp only [warpIndex,Nat.div_div_eq_div_mul,show 32*4 = 128 by decide]
    exact scoreProbabilityWriteOrder hX hPhase (firstScoreConsumerStage hp hX hPhase)
      hWaitRead hReadComplete hWaitLd q word quarter hWrittenStage he hLen hWrite
  · have hCellCta := congrArg Cell.cta hCell
    simp only [tcDataCell_cta] at hCellCta
    have hCta : g / l.block = producer / l.block :=
      hCellCta.symm.trans hPhase.sameCta.2.2.symm
    exact (singleVisitNoCorrectionStore hp hX hFrame (i := (g,j)) hb
      (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip) writtenStage chunk he).elim

end PTX.Kernels.TmlFa4Fwd.Softmax
