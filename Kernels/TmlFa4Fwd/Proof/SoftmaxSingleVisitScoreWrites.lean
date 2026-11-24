-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitScore
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPhase
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
import Kernels.TmlFa4Fwd.Proof.SoftmaxInitialQkWriters
import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedScoreWrites
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueByteOperands
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueSites
import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailDestination

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma
open Epilogue (assignedCoordinates)

/-- Decoded MMA instructions in the steady body all require entry to the steady PV route. -/
private theorem mmaIssueInSteadyBody {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc d : Nat}
    {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get i = some ⟨pc,.tc (.mma d op acc mask)⟩) (hLo : 2279 ≤ pc) : 2295 ≤ pc := by
  obtain ⟨bank,frag,hSite | hSite⟩ := Thread.Mma.mmaIssueBank hX he
  · rw [hSite] at hLo ⊢
    fin_cases bank <;> fin_cases frag <;> simp [Mma.qkPc] at hLo ⊢
  · rw [hSite]
    fin_cases bank <;> fin_cases frag <;> decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFrame : OutputFootprint p X) {batch : Nat} {stage : Fin 2}
include hp hX hDone hFrame

/-- A single-visit score cell's MMA writers are the eight initial QK fragments once
the two tail PV destinations have been identified by the actual output broadcasts. -/
theorem singleVisitScoreMmaWriter {producer consumer commit wait start : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (producer / l.block)).1 = 1)
    (hPhase : FirstQkPhase l X stage producer consumer commit wait) {output : EvId}
    {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer / l.block = output.1 / l.block)
    (hIssues : ∀ frag : Fin 8, X.get (producer,start+frag.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) frag 0)) (q : Fin 4) (word : Fin 32)
    {other : EvId}
    (hWrite : X.MmaCell other (tcDataCell l consumer .s32x32b
      (scoreAddress l consumer stage q) word.val)) :
    ∃ frag : Fin 8, other = (producer,start+frag.val) := by
  have hScore : (tcDataCell l consumer .s32x32b
      (scoreAddress l consumer stage q) word.val).cta = consumer / l.block := by
    have hColumn := scoreColumn_range stage
    have hQuarter := q.isLt
    rw [scoreAddress,tcDataCell_warp32 _ _ _ (by omega)]
  have hCta : other.1 / l.block = producer / l.block :=
    (mmaWriteCta hp hX hWrite).symm.trans (hScore.trans hPhase.sameCta.2.2.symm)
  have hRecord := hWrite
  obtain ⟨d,op,acc,mask,_,_,⟨pc,he⟩,_⟩ := hRecord
  have hVisit : pc < 2279 ∨ 2534 ≤ pc := by
    by_contra! hVisit
    obtain ⟨g,j⟩ := other
    apply singleVisitNoSteadyEvent hp hX hDone hFrame hb
      (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip) he
    exact ⟨mmaIssueInSteadyBody hX he hVisit.1,hVisit.2⟩
  rcases Thread.Mma.singleVisitMmaIssueBank hX he hVisit with
    ⟨writtenStage,frag,rfl⟩ | ⟨writtenStage,frag,rfl⟩
  · exact initialQkCompetingWriter hp hX hPhase hOutput hOutputCta hIssues
      q word writtenStage frag he hWrite
  · have hBlock : (⟨2 + writtenStage.val,by have := writtenStage.isLt; omega⟩ : Fin 4) =
        Thread.firstPvBlock false writtenStage :=
      Fin.ext (by simp [Thread.firstPvBlock,Nat.add_comm])
    have hValue : Thread.InitialValueFragment X other false writtenStage frag d op acc mask := by
      unfold Thread.InitialValueFragment
      exact hBlock ▸ he
    have hDesc := (hValue.valueLayout hp hX).1
    have hPv : Thread.PvInstruction X other (Thread.firstPvBlock false writtenStage)
        frag d op acc mask := Thread.PvInstruction.of_decoded hValue
    have hD := hPv.tailOutputDestination hp hX writtenStage
    exact (scorePvDisjoint consumer stage writtenStage q word hDesc
      ⟨_,hD ▸ he⟩ hWrite).elim

/-- The only outside writers of the first score cell are ordered probability stores. -/
theorem singleVisitScoreOutsideWrites {producer consumer commit wait read complete start : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (producer / l.block)).1 = 1)
    (hPhase : FirstQkPhase l X stage producer consumer commit wait) {output : EvId}
    {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer / l.block = output.1 / l.block)
    (hIssues : ∀ frag : Fin 8, X.get (producer,start+frag.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) frag 0)) (hWaitRead : wait < read)
    (hReadComplete : read < complete)
    (hWaitLd : X.get (consumer,complete) = some ⟨4826,.tc .waitLd⟩) (q : Fin 4) (word : Fin 32) :
    InitialScoreOtherWrites l X producer start consumer read
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val) := by
  let cell := tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val
  have hStore {other : EvId} (hWrite : StoreCell l X other cell) :=
    singleVisitScoreStoreOrdering hp hX hFrame hb hLo hHi hTrip hPhase
      hWaitRead hReadComplete hWaitLd q word hWrite
  have hMma {other : EvId} (hWrite : X.MmaCell other cell)
      (hOther : ∀ frag : Fin 8, other ≠ (producer,start+frag.val)) : False := by
    obtain ⟨frag,hId⟩ := singleVisitScoreMmaWriter hp hX hDone hFrame hb hLo hHi hTrip
      hPhase hOutput hOutputCta hIssues q word hWrite
    exact hOther frag hId
  constructor
  · intro step _ other hWrite hOther
    rcases hWrite with hWrite | hWrite
    · exact (hMma hWrite hOther).elim
    · have hBefore := firstObservedQkBeforeCommit hX hPhase step (hIssues step)
      refine .inr ((hStore hWrite).2 _ hBefore ?_)
      exact .inl ⟨scoreColumn (Mma.qkStage (firstQkBlock stage)),
        Mma.qkOperands l producer (firstQkBlock stage) step 0,decide (step.val ≠ 0),
        List.replicate 4 0,_,hIssues step⟩
  · intro other hWrite hOther
    rcases hWrite with hWrite | hWrite
    · exact (hMma hWrite hOther).elim
    · exact .inr (hStore hWrite).1

end PTX.Kernels.TmlFa4Fwd.Softmax
