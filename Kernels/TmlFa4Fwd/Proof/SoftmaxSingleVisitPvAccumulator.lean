-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitPvWriters
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvCarry
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma Thread Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- The issue order of a tail fragment pair orders its common accumulator. -/
theorem tailPvPipeline {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {i j : EvId} {a b : Fin 8} {d d' : Nat}
    {op op' : OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    (hi : PvInstruction X i (firstPvBlock false stage) a d op acc mask)
    (hj : PvInstruction X j (firstPvBlock false stage) b d' op' acc' mask')
    (hCta : i.1/l.block = j.1/l.block) (hLt : a.val < b.val) :
    Pipelined l X .dWrite i .dWrite j := by
  have hOrder := hi.tailTraceOrder hp hX stage hj hCta hLt
  have hi' := hi.decoded
  have hj' := hj.decoded
  have hPo := po_of_not_access hOrder.1 hOrder.2.1 hOrder.2.2 (by rw [hj']; rfl)
  have hWarp : SameWarp l i.1 j.1 := ⟨⟨event_thread_lt hX hi',event_thread_lt hX hj',hCta⟩,
    by rw [hOrder.1]⟩
  have hDst := (hi.tailOutputDestination hp hX stage).trans
    (hj.tailOutputDestination hp hX stage).symm
  obtain ⟨_,_,hDesc,hLow,hHigh⟩ := hi.valueOperand hp hX
  obtain ⟨_,_,hDesc',hLow',hHigh'⟩ := hj.valueOperand hp hX
  have hAcc : SameAccumulator d op d' op' := ⟨hDst,by rw [hDesc,hDesc'],by rw [hDesc,hDesc'],
      hLow.trans (hCta.trans hLow'.symm),hHigh.trans (hCta.trans hHigh'.symm)⟩
  exact ⟨hWarp,.inl (.single (.inl hPo)),d,op,acc,mask,d',op',acc',mask',
    ⟨_,hi'⟩,⟨_,hj'⟩,hAcc⟩

/-- Each accumulating tail PV fragment of a one-visit tile reads the preceding
fragment's output. No other Tensor Memory writer can intervene. -/
theorem singleVisitPvAccumulatorSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch cta : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1)
    (stage : Fin 2) (row col : Fin 128) {i j : EvId} {a b : Fin 8}
    {d d' : Nat} {op op' : OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    (hi : PvInstruction X i (firstPvBlock false stage) a d op acc mask)
    (hj : PvInstruction X j (firstPvBlock false stage) b d' op' acc' mask')
    (hI : i.1/l.block = cta) (hJ : j.1/l.block = cta) (hNext : a.val+1 = b.val) :
    ReadSource l X .acc i j ⟨cta,row.val,outputColumn stage+col.val⟩ := by
  have hCta := hI.trans hJ.symm
  have hLt : a.val < b.val := by omega
  have hTrace := hi.tailTraceOrder hp hX stage hj hCta hLt
  have hNe : i ≠ j := by intro h; exact (Nat.ne_of_lt hTrace.2.1) (congrArg Prod.snd h)
  have hMask := (hi.fixedOperandFields hX).2.2
  have hWrite := hi.outputCell hp hX row col
  have hStage : (pvSite (firstPvBlock false stage)).stage = stage := by fin_cases stage <;> rfl
  rw [hI,hStage] at hWrite
  obtain ⟨_,_,hDesc,_,_⟩ := hi.valueOperand hp hX
  have hGroup : op.descriptor.group = .one := by rw [hDesc]; rfl
  have hRows : op.descriptor.m = 128 := by rw [hDesc]; rfl
  have hWrites := writeCell_no_mask_128 hGroup hRows row.isLt row.isLt hWrite
  rw [← hMask] at hWrites
  have hProducer : X.MmaCell i ⟨cta,row.val,outputColumn stage+col.val⟩ :=
    ⟨d,op,acc,mask,row,col,⟨_,hi.decoded⟩,hWrites⟩
  have hPipe := tailPvPipeline hp hX stage hi hj hCta hLt
  have hAcc : acc' = true := (hj.accumulatorUse hp hX).mpr (.inl (by omega))
  have hRead := hj.outputCell hp hX row col
  rw [hJ,hStage] at hRead
  have hConsume : X.MmaReadCell j ⟨cta,row.val,outputColumn stage+col.val⟩ :=
    ⟨d',op',mask',row,col,⟨_,hAcc ▸ hj.decoded⟩,hRead⟩
  have hLife := (Safety.mmaAccessLifetime hp hX (hFrame.metadataProtected hp).1
    (.inr (.inl hConsume))).2
  refine ⟨hNe,.inl hProducer,.inl (.inr hPipe),?_,?_⟩
  · intro other hw
    obtain ⟨hOwner,step,d₀,op₀,acc₀,mask₀,hOther⟩ :=
      singleVisitOutputWriter hp hX hDone hFrame hb hLo hHi hTrip stage row col hw
    rcases lt_trichotomy step.val a.val with hLt | hSame | hGt
    · exact .inr (.inl (.inl (.inr
        (tailPvPipeline hp hX stage hOther hi (hOwner.trans hI.symm) hLt))))
    · obtain rfl : step = a := Fin.ext hSame
      exact .inl (hOther.tailUnique hp hX stage hi (hOwner.trans hI.symm))
    · rcases Nat.eq_or_lt_of_le (show b.val ≤ step.val by omega) with hSame | hAfter
      · obtain rfl : step = b := Fin.ext hSame.symm
        exact .inr (.inr (.inl (hOther.tailUnique hp hX stage hj (hOwner.trans hJ.symm))))
      · exact .inr (.inr (.inr (.inr
          (tailPvPipeline hp hX stage hj hOther (hJ.trans hOwner.symm) hAfter))))
  · intro c r hr hCover release hRelease
    exact .inl (hLife c r hr hCover release hRelease)

end PTX.Kernels.TmlFa4Fwd.Softmax
