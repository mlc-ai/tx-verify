-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaOperandRange
import Kernels.TmlFa4Fwd.Flow.Sites.Part000
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.NotTcCp
import Lemmas.Flow.NotTcMma
import Lemmas.Tcgen05.MmaBytePair

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Mma (qkPc pvPc)

noncomputable section

/-- No decoded instruction in this kernel can issue a shared Tensor Core copy. -/
theorem noTensorCopyOperandIssue {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {s : TcCopy.Spec} :
    ¬ X.CpIssue i s := by
  rintro ⟨_,hGet⟩
  rcases get_source hX hGet with ⟨_,hFault⟩ | ⟨_,ins,_,_,hCode,hFire⟩
  · cases hFault
  have hOp := fires_tcCp_op hFire rfl
  have hAll : kernel.code.all (fun n => !tcCpOp n.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hNone := List.all_eq_true.mp hAll ins (List.mem_of_getElem? hCode)
  simp [hOp] at hNone

/-- Each pending shared operand footprint comes from an actual dense MMA issue. -/
theorem mmaSharedFootprintIssue {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {isB : Bool} {index : Nat} {loc : Loc} (h : X.MmaFootprint i isB index loc) :
    loc.space = .shared ∧ ∃ d op accum mask, X.MmaIssue i d op accum mask ∧
      op.byteLoc (if isB then .b else .a) index = some loc := by
  rcases h with ⟨d,op,accum,mask,hIssue,hLoc⟩ | ⟨spec,_,_,hCopy,_,_,_,_⟩
  · exact ⟨TcMma.OperandSpec.byteLoc_shared hLoc,d,op,accum,mask,hIssue,hLoc⟩
  · exact (noTensorCopyOperandIssue hX hCopy).elim

/-- The fragment station of an actual query-key contraction. -/
@[no_expose] def QkInstruction (X : Execution) (i : EvId) (block : Fin 4) (step : Fin 8)
    (d : Nat) (op : TcMma.OperandSpec) (accum : Bool) (mask : List Nat) : Prop :=
  X.get i = some ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩

/-- The fragment station of an actual probability-value contraction. -/
@[no_expose] def PvInstruction (X : Execution) (i : EvId) (block : Fin 4) (step : Fin 8)
    (d : Nat) (op : TcMma.OperandSpec) (accum : Bool) (mask : List Nat) : Prop :=
  X.get i = some ⟨pvPc block step,.tc (.mma d op accum mask)⟩

/-- Recover the issued QK instruction within the thread proof layer. -/
theorem QkInstruction.decoded {X : Execution} {i : EvId} {block : Fin 4} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : QkInstruction X i block step d op accum mask) :
    X.get i = some ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩ := h

theorem QkInstruction.of_decoded {X : Execution} {i : EvId} {block : Fin 4}
    {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : X.get i = some ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩) :
    QkInstruction X i block step d op accum mask := h

/-- Recover the issued PV instruction within the thread proof layer. -/
theorem PvInstruction.decoded {X : Execution} {i : EvId} {block : Fin 4} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : PvInstruction X i block step d op accum mask) :
    X.get i = some ⟨pvPc block step,.tc (.mma d op accum mask)⟩ := h

theorem PvInstruction.of_decoded {X : Execution} {i : EvId} {block : Fin 4}
    {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : X.get i = some ⟨pvPc block step,.tc (.mma d op accum mask)⟩) :
    PvInstruction X i block step d op accum mask := h

/-- The recorded dense MMA sites consist of the four QK and four PV fragment groups. -/
theorem actualMmaInstruction {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hMma : X.MmaIssue i d op accum mask) :
    (∃ block step, QkInstruction X i block step d op accum mask) ∨
      ∃ block step, PvInstruction X i block step d op accum mask := by
  obtain ⟨site,hGet⟩ := hMma
  rcases get_source hX hGet with ⟨_,hFault⟩ | ⟨_,_,_,_,hCode,hFire⟩
  · cases hFault
  have hTable : OpPcsFast kernel.code tcMmaOp Flow.mma.toList = true := by decide +kernel
  have hMember := OpPcsFast.mem hTable hCode (fires_tcMma_op hFire rfl)
  have hCover : Flow.mma.toList.all (fun pos => (List.finRange 4).any (fun block =>
      (List.finRange 8).any (fun frag => pos == qkPc block+frag.val || pos == pvPc block frag))) =
      true := by decide +kernel
  obtain ⟨block,_,hBlock⟩ := List.any_eq_true.mp (List.all_eq_true.mp hCover site hMember)
  obtain ⟨frag,_,hFrag⟩ := List.any_eq_true.mp hBlock
  rw [Bool.or_eq_true] at hFrag
  rcases hFrag with hQuery | hValue
  · have hs : site = qkPc block+frag.val := beq_iff_eq.mp hQuery
    subst site
    exact .inl ⟨block,frag,hGet⟩
  · have hs : site = pvPc block frag := beq_iff_eq.mp hValue
    subst site
    exact .inr ⟨block,frag,hGet⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
