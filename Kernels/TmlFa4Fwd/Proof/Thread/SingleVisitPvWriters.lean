-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TailPvIssueOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitCorrectionWrites
import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPhase
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.TcMma Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem outputColumnsRange (stage : Fin 2) (col : Fin 128) :
    256 ≤ outputColumn stage + col.val ∧ outputColumn stage + col.val < 512 := by
  have h := col.isLt
  fin_cases stage <;> unfold outputColumn <;> dsimp <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Only a tail group of this output stage can write this single-visit result cell. -/
theorem singleVisitOutputMmaWriter (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X) {batch cta : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch cta).1 = 1) (stage : Fin 2)
    (row col : Fin 128) {i : EvId} (hWrite : X.MmaCell i ⟨cta,row.val,outputColumn stage+col.val⟩) :
    i.1/l.block = cta ∧
      ∃ step d op acc mask, PvInstruction X i (firstPvBlock false stage) step d op acc mask := by
  obtain ⟨d,op,acc,mask,r,c,hIssue,hw⟩ := hWrite
  have hResult := writeCell_resultCell hw
  obtain ⟨hR,hC⟩ := resultCell_rowcol hResult
  have hOutput := outputColumnsRange stage col
  rcases actualMmaInstruction hX hIssue with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · have hDesc := (hQk.queryOperand hp hX).descriptor
    have hR' : r < 128 := by simpa [hDesc,qkDescriptor] using hR
    have hC' : c < 128 := by simpa [hDesc,qkDescriptor] using hC
    have hColumn := congrArg Cell.column (Option.some.inj
      (hResult.symm.trans (hQk.scoreCell hp hX ⟨r,hR'⟩ ⟨c,hC'⟩)))
    change outputColumn stage+col.val = scoreColumn (qkStage block)+c at hColumn
    have := scoreColumn_range (qkStage block)
    omega
  · obtain ⟨_,_,hDesc,_,_⟩ := hPv.valueOperand hp hX
    have hR' : r < 128 := by simpa [hDesc,pvDescriptor] using hR
    have hC' : c < 128 := by simpa [hDesc,pvDescriptor] using hC
    have hCell := Option.some.inj
      (hResult.symm.trans (hPv.outputCell hp hX ⟨r,hR'⟩ ⟨c,hC'⟩))
    have hCta : i.1/l.block = cta := (congrArg Cell.cta hCell).symm
    have hColumn : outputColumn stage+col.val = outputColumn (pvSite block).stage+c :=
      congrArg Cell.column hCell
    have hStage : (pvSite block).stage = stage := by
      fin_cases stage <;> fin_cases block <;> first
        | rfl
        | (simp [pvSite,outputColumn] at hColumn; have := col.isLt; omega)
    have hTail : 2 ≤ block.val := by
      by_contra! hSteady
      have audit : ∀ b : Fin 4, ∀ f : Fin 8, b.val < 2 →
          2295 ≤ pvPc b f ∧ pvPc b f < 2534 := by decide
      have hPc := audit block step hSteady
      exact Softmax.singleVisitNoSteadyEvent hp hX hDone hFrame hb (hCta.symm ▸ hLo)
        (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip) hPv.decoded hPc
    have audit : ∀ b : Fin 4, ∀ s : Fin 2, 2 ≤ b.val → (pvSite b).stage = s →
        b = firstPvBlock false s := by decide
    have hBlock := audit block stage hTail hStage
    exact ⟨hCta,step,d,op,acc,mask,hBlock ▸ hPv⟩

private theorem noOutputStore (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {batch cta : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch cta).1 = 1) (stage : Fin 2)
    (row col : Fin 128) {i : EvId}
    (hWrite : StoreCell l X i ⟨cta,row.val,outputColumn stage+col.val⟩) : False := by
  obtain ⟨addr,vals,shape,j,⟨site,he⟩,hLength,hCell⟩ := hWrite
  have hCta : i.1/l.block = cta := (congrArg Cell.cta hCell).symm
  rcases tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨s,k,rfl⟩
  · obtain ⟨warp,_,rfl,hCount,rfl⟩ := Scores.probabilityStoreAddress hp hX round q he
    have hS := scoreColumn_range (Softmax.stageOf warp)
    have hQ := q.isLt
    have hAddr : probabilityColumn (Softmax.stageOf warp)+16*q.val < 512 := by
      unfold probabilityColumn
      omega
    rw [Softmax.probabilityAddress,tcDataCell_warp32 l i.1 j hAddr] at hCell
    symm at hCell
    have hColumn := congrArg Cell.column hCell
    have hTarget := outputColumnsRange stage col
    rw [hCount] at hLength
    change probabilityColumn (Softmax.stageOf warp)+16*q.val+j =
      outputColumn stage+col.val at hColumn
    unfold probabilityColumn at hColumn
    omega
  · exact Softmax.singleVisitNoCorrectionStore hp hX hFrame hb (hCta.symm ▸ hLo)
      (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip) s k he

/-- Every write to an output cell of a single-visit tile is a PV fragment of that stage. -/
theorem singleVisitOutputWriter (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X) {batch cta : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch cta).1 = 1) (stage : Fin 2)
    (row col : Fin 128) {i : EvId}
    (hWrite : TmemWrite l X i ⟨cta,row.val,outputColumn stage+col.val⟩) :
    i.1/l.block = cta ∧
      ∃ step d op acc mask, PvInstruction X i (firstPvBlock false stage) step d op acc mask := by
  rcases hWrite with hMma | hStore | hCopy | hShift
  · exact singleVisitOutputMmaWriter hp hX hDone hFrame hb hLo hHi hTrip stage row col hMma
  · exact (noOutputStore hp hX hFrame hb hLo hHi hTrip stage row col hStore).elim
  · obtain ⟨_,_,_,_,hCopy,_⟩ := hCopy
    exact (noTensorCopyOperandIssue hX hCopy).elim
  · obtain ⟨_,hShift,_⟩ := hShift
    exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Thread
