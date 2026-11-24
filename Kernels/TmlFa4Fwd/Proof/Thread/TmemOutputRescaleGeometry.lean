-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreCompletion
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.TcMma Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- A real store in an output-rescale tile has that stage's correction-store opcode. -/
theorem outputRescaleStoreOfCell {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {store : EvId} {cell : Cell}
    (hStore : StoreCell l X store cell)
    (hFoot : TensorStoreFootprint l store cell (.rescale stage)) :
    OutputRescaleStore X store stage := by
  have hGroup := hFoot.warpGroup
  obtain ⟨address,values,shape,z,⟨site,he⟩,hz,rfl⟩ := hStore
  rcases tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨other,k,rfl⟩
  · obtain ⟨w,hWarp,_,_,_⟩ := Scores.probabilityStoreAddress hp hX round q he
    have hSoft : warpIndex l store.1 < 8 := hWarp ▸ w.isLt
    change (store.1%l.block)/128 = 2 at hGroup
    unfold warpIndex at hSoft
    omega
  · obtain ⟨rfl,rfl,hLength⟩ := Correction.rescaleStoreActualAddress hp hX other k he
    have hRange := outputColumn_range other
    have hChunk := k.isLt
    rw [hLength] at hz
    have hLo := hFoot.columnLo
    have hHi := hFoot.columnHi
    have hColumn : outputColumn other + 16*k.val < 512 := by omega
    unfold Correction.outputAddress at hLo hHi
    rw [tcDataCell_warp32 l store.1 z hColumn] at hLo hHi
    change outputColumn stage ≤ outputColumn other+16*k.val+z at hLo
    change outputColumn other+16*k.val+z < outputColumn stage+128 at hHi
    have hStage : other = stage := by
      fin_cases other <;> fin_cases stage <;> first | rfl |
        (simp [outputColumn] at hLo hHi; omega)
    subst other
    exact OutputRescaleStore.ofDecoded stage k he

/-- A PV issue overlaps its own CTA's rescale store and provides the actual
joint probability guard for that stage in the steady or tail body. -/
theorem outputRescaleOverlap {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {mma store : EvId} {cell : Cell}
    (hStore : StoreCell l X store cell)
    (hFoot : TensorStoreFootprint l store cell (.rescale stage))
    (hOverlap : MmaAccumulatorOn X mma cell (.rescale stage)) :
    ∃ d op acc mask wait, X.MmaIssue mma d op acc mask ∧ SameCta l mma.1 store.1 ∧
      OutputRescaleStore X store stage ∧ MmaProbabilityAcquire l X mma stage 0 wait := by
  obtain ⟨block,frag,d,op,acc,mask,row,col,hStage,hPv,hCell⟩ := hOverlap
  obtain ⟨_,_,_,hLow,hHigh⟩ := hPv.valueOperand hp hX
  have hOwner : cell.cta = mma.1/l.block := by
    rcases resultCell_cta hCell with hLo | hHi
    · exact hLo.trans hLow
    · exact hHi.trans hHigh
  have hRescale := outputRescaleStoreOfCell hp hX hStore hFoot
  obtain ⟨_,_,_,_,⟨_,he⟩,_,_⟩ := hStore
  have hSame : SameCta l mma.1 store.1 :=
    ⟨event_thread_lt hX hPv.decoded,event_thread_lt hX he,hOwner.symm.trans hFoot.cta⟩
  have hBank : ∃ steady : Bool, block = firstPvBlock steady stage := by
    fin_cases block <;> fin_cases stage <;>
      first | exact ⟨true,rfl⟩ | exact ⟨false,rfl⟩ | cases hStage
  obtain ⟨steady,rfl⟩ := hBank
  have hAcquire : ∃ wait, MmaProbabilityAcquire l X mma stage 0 wait := by
    cases steady
    · exact hPv.tailJointProbabilityAcquire hp hX stage
    · exact hPv.steadyProbabilityAcquire hp hX stage 0 (.inl rfl)
  obtain ⟨wait,hGuard⟩ := hAcquire
  exact ⟨d,op,acc,mask,wait,⟨_,hPv.decoded⟩,hSame,hRescale,hGuard⟩

end PTX.Kernels.TmlFa4Fwd.Thread
