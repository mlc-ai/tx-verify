-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitQkValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxInitialScoreLifetime

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma
open Epilogue (assignedCoordinates)

/-- The remaining ordering facts concern only writes outside the eight initial QK fragments. -/
structure InitialScoreOtherWrites (l : Launch) (X : Execution)
    (producer start consumer read : Nat) (cell : Cell) : Prop where
  accumulator : ∀ (step : Fin 8), step.val ≠ 0 → ∀ other,
    (X.MmaCell other cell ∨ StoreCell l X other cell) →
      (∀ k : Fin 8, other ≠ (producer,start+k.val)) →
      WriteBefore l X other (producer,start+(step.val-1)) ∨
        ReadBefore l X .acc (producer,start+step.val) other
  load : ∀ other, (X.MmaCell other cell ∨ StoreCell l X other cell) →
    (∀ k : Fin 8, other ≠ (producer,start+k.val)) →
      WriteBefore l X other (producer,start+7) ∨ ReadBefore l X .ld (consumer,read) other

/-- The initial score notification identifies the actual QK bank. The companion wait and
the CTA's final barrier establish liveness for the accumulator chain and observed load. -/
theorem singleVisitScoreWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch : Nat} {stage : Fin 2} {producer consumer commit wait read complete : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (producer / l.block)).1 = 1)
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    {output : EvId} {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer / l.block = output.1 / l.block)
    (q : Fin 4) (word : Fin 32) {vals : List Value}
    (he : X.get (consumer,read) = some
      ⟨scorePc .first q,.tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hAfter : wait < read) (hComplete : X.get (consumer,complete) = some ⟨4826,.tc .waitLd⟩)
    (hLater : read < complete)
    (hOutside : ∀ start, (∀ step : Fin 8, X.get (producer,start+step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step 0)) →
      InitialScoreOtherWrites l X producer start consumer read
        (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    let coords := assignedCoordinates p batch (producer / l.block)
    let firstQ := p.qOffset batch + 256 * coords.1 + 128 * stage.val
    vals[word.val]? =
      some (.float .f32 (firstScoreDot p l consumer batch coords.2 firstQ 0 q word)) := by
  let cell := tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val
  have hOwner : cell.cta = consumer / l.block := by
    have hCol := scoreColumn_range stage
    have hQuarter := q.isLt
    change (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val).cta = _
    rw [scoreAddress,tcDataCell_warp32 _ _ _ (by omega)]
  obtain ⟨start,hIssues⟩ := firstObservedQkIssues hp hX hPhase hOutput hOutputCta
  have hOther := hOutside start hIssues
  have hLoad : X.TLd (consumer,read) (scoreAddress l consumer stage q) vals .s32x32b := ⟨_,he⟩
  refine firstObservedSingleVisitScoreWord hp hX hDone hFrame hb hLo hHi hTrip
    hPhase hOutput hOutputCta hAfter hIssues q word he ?_ hOther.load
      (initialScoreLoadLive hp hX hOwner hLoad hComplete hLater)
  intro step hStep
  have hBefore := firstObservedQkBeforeCommit hX hPhase step (hIssues step)
  have hIssue : X.MmaIssue (producer,start+step.val)
      (scoreColumn stage) (Mma.qkOperands l producer (firstQkBlock stage) step 0)
      (decide (step.val ≠ 0)) (List.replicate 4 0) := by
    refine ⟨Mma.qkPc (firstQkBlock stage)+step.val,?_⟩
    simpa only [Mma.qkIssueEvent,firstQkBlock_stage] using hIssues step
  exact firstScoreAccumulatorSource hX hPhase.sameCta hIssues q word step hStep
    (hOther.accumulator step hStep)
    (initialScoreAccumulatorLive hp hX hPhase hIssue hBefore q he hAfter hOwner)

end PTX.Kernels.TmlFa4Fwd.Softmax
