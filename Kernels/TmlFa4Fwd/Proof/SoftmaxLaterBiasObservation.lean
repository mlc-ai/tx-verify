-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxTailBiasWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Loader Thread Thread.Scores Thread.Loader
open Protocol.Bias

/-- An actual Bias word at a positive rendezvous ordinal contains the two logical
Bias entries for that visit, including the low stage's optional extra Bias visit. -/
theorem observedLaterBiasWordInRange {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    {g read : Nat} {repeated : Bool} {i : Fin 16} {access : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X (g,read) repeated i access bytes) :
    ∃ (warp : Fin 8) (word : Fin 4),
      let stage := stageOf warp
      let visit := observedBarrierOrdinal X (g,read) (11+stage.val)
      warp.val = warpIndex l g ∧
      access = biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val ∧
      (0 < visit →
        ∃ batch < p.batch,
          tilePrefix p batch*p.heads ≤ g/l.block ∧
          g/l.block < tilePrefix p (batch+1)*p.heads ∧
          let co := assignedCoordinates p batch (g/l.block)
          let row := 256*co.1+128*stage.val+(g%l.block)%128
          let col := 8*i.val+2*word.val
          visit < Mma.trips p batch co.1 ∧
          visit < Mma.trips p batch co.1-stageGeometryBlocks p batch co.1 stage+10 ∧
          rebuild 3 bytes = .ok (biasLoadWord
            (visitBiasElement p batch co.1 row co.2 visit col)
            (visitBiasElement p batch co.1 row co.2 visit (col+1)))) := by
  obtain ⟨warp,word,wait,tensor,o,hWarp,hAccess,hBefore,hBox,hOrdinal,hOrder⟩ :=
    biasWordObservedOrder hp hX hRead
  let stage := stageOf warp
  let visit := observedBarrierOrdinal X (g,read) (11+stage.val)
  let half := biasVectorHalf i
  refine ⟨warp,word,hWarp,hAccess,?_⟩
  intro hPositive
  change ∃ batch < p.batch,
    tilePrefix p batch*p.heads ≤ g/l.block ∧
    g/l.block < tilePrefix p (batch+1)*p.heads ∧
    let co := assignedCoordinates p batch (g/l.block)
    let row := 256*co.1+128*stage.val+(g%l.block)%128
    let col := 8*i.val+2*word.val
    visit < Mma.trips p batch co.1 ∧
    visit < Mma.trips p batch co.1-stageGeometryBlocks p batch co.1 stage+10 ∧
    rebuild 3 bytes = .ok (biasLoadWord
      (visitBiasElement p batch co.1 row co.2 visit col)
      (visitBiasElement p batch co.1 row co.2 visit (col+1)))
  have hRead' : BiasVectorRead X (g,read) repeated i
      (biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val) bytes :=
    hAccess ▸ hRead
  obtain ⟨site,hStage,hHalf,hIssue⟩ := biasTensorSelectorOfSubbox hp hX hBox.subbox
  have classifies (j : Fin 10) :
      let s := biasTensorSelector j
      s.issue = (inputSite (firstBiasIssueSite s.stage s.half)).pc ∨
        s.issue = warmBiasIssueSite s.stage s.half ∨
        (s.stage = 0 ∧ s.issue = (inputSite (tailBiasInputSite s.half)).pc) := by
    fin_cases j <;> decide
  have hWhich :
      (biasTensorSelector site).issue = (inputSite (firstBiasIssueSite stage half)).pc ∨
        (biasTensorSelector site).issue = warmBiasIssueSite stage half ∨
        (stage = 0 ∧ (biasTensorSelector site).issue = (inputSite (tailBiasInputSite half)).pc) :=
    by
      have hs : (biasTensorSelector site).stage = stage := hStage
      have hh : (biasTensorSelector site).half = half := hHalf
      exact by simpa only [hs,hh] using classifies site
  change 0 < visit at hPositive
  change biasTensorOrdinal l X stage half tensor = visit at hOrdinal
  rcases hWhich with hFirst | hWarm | ⟨hLow,hTail⟩
  · rw [hFirst] at hIssue
    have hZero : biasTensorOrdinal l X stage half tensor = 0 :=
      biasPrimingOrdinalZero hp hX stage half hIssue
    rw [hZero] at hOrdinal
    omega
  · rw [hWarm] at hIssue
    obtain ⟨batch,hb,hLo,hHi,iteration,hIter,hWarmOrdinal,hValue⟩ :=
      warmBiasWordOfSelectedHalf hp hX hFrame hCuQ hRead' hBefore hBox hOrder hIssue
    have hVisit : visit = iteration+1 := hOrdinal.symm.trans hWarmOrdinal
    rw [hVisit]
    exact ⟨batch,hb,hLo,hHi,by omega,by omega,hValue⟩
  · rw [hTail] at hIssue
    change AcquiredBiasBox p l X stage g wait tensor half o at hBox
    change BiasWordOrder p l X stage repeated i word g read tensor at hOrder
    rw [hLow] at hRead' hBox hOrder hOrdinal
    obtain ⟨owner,ho,hOwnerLo,hOwnerHi,_,hResidual,_⟩ :=
      tailBiasFinalOrigin hp hX hFrame hCuQ half hBox.subbox hIssue
    rw [hBox.owner] at hOwnerLo hOwnerHi hResidual
    obtain ⟨batch,hb,hLo,hHi,hTrips,hTailOrdinal,hValue⟩ :=
      tailBiasWordOfSelectedHalf hp hX hFrame hCuQ hRead' hBefore hBox hOrder hIssue
    have hVisit : visit = 10 := hOrdinal.symm.trans hTailOrdinal
    rw [hVisit,hLow]
    have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
      hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
    obtain ⟨chosen,_,hUnique⟩ := tileBatch_existsUnique p hActive
    have hBatch := (hUnique owner ⟨ho,hOwnerLo,hOwnerHi⟩).trans
      (hUnique batch ⟨hb,hLo,hHi⟩).symm
    subst owner
    have hGeom := (stageGeometryBiasAdjustment p batch (assignedCoordinates p batch
      (g/l.block)).1 0).2
    simp only [ite_true,hResidual] at hGeom
    exact ⟨batch,hb,hLo,hHi,hTrips,by omega,hValue⟩

/-- Read the two logical Bias entries without retaining the strict biased-extent bound. -/
theorem observedLaterBiasWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    {g read : Nat} {repeated : Bool} {i : Fin 16} {access : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X (g,read) repeated i access bytes) :
    ∃ (warp : Fin 8) (word : Fin 4),
      let stage := stageOf warp
      let visit := observedBarrierOrdinal X (g,read) (11+stage.val)
      warp.val = warpIndex l g ∧
      access = biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val ∧
      (0 < visit →
        ∃ batch < p.batch,
          tilePrefix p batch*p.heads ≤ g/l.block ∧
          g/l.block < tilePrefix p (batch+1)*p.heads ∧
          let co := assignedCoordinates p batch (g/l.block)
          let row := 256*co.1+128*stage.val+(g%l.block)%128
          let col := 8*i.val+2*word.val
          visit < Mma.trips p batch co.1 ∧
          rebuild 3 bytes = .ok (biasLoadWord
            (visitBiasElement p batch co.1 row co.2 visit col)
            (visitBiasElement p batch co.1 row co.2 visit (col+1)))) := by

  obtain ⟨warp,word,hWarp,hAccess,hWords⟩ := observedLaterBiasWordInRange hp hX hFrame hCuQ hRead
  refine ⟨warp,word,hWarp,hAccess,fun hPositive => ?_⟩
  obtain ⟨batch,hb,hLo,hHi,hTrips,_,hWords⟩ := hWords hPositive
  exact ⟨batch,hb,hLo,hHi,hTrips,hWords⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
