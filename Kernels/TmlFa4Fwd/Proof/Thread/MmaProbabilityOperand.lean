-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Lemmas.Flow.TcTmpl
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma (pvCode)

noncomputable section

private def hasTensorA : Tmpl → Prop
  | .tc (.mma _ op _ _) _ => op.aTmem.isSome = true
  | .ub _ => True
  | _ => False

private theorem ofExecHasTensorA {r : Exec Tmpl} (h : AllOk hasTensorA r) :
    hasTensorA (ofExec r) := by
  cases r
  · trivial
  · exact h

private theorem tmemTemplateHasTensorA {l : Launch} {g d ta : Nat} {t : TState} {off : Int}
    {bd id en : Opnd} {mask : List Opnd} :
    hasTensorA (eventTmpl Assumptions.all l g t
      (.tcMma (.dense .one false .f16 d (.tmem ta off) bd id mask en))) := by
  simp only [eventTmpl,tcTmpl_tcMma_tmem (.inr (.inl rfl)),mmaTmemTmpl]
  apply ofExecHasTensorA
  by_cases hThread : g < l.threads
  · simp only [hThread,↓reduceIte]
    apply allOk_bind
    intro dst
    apply allOk_bind
    intro tensor
    apply allOk_bind (r := tmemOffset tensor.toNat off)
    intro a
    apply allOk_bind (r := readBits l g t 64 bd)
    intro b
    apply allOk_bind (r := readBits l g t 32 id)
    intro i
    apply allOk_bind (r := mask.mapM (readBits l g t 32))
    intro masks
    by_cases hCount : mask.length = 4 * CtaGroup.one.size
    · simp only [hCount,↓reduceIte]
      apply allOk_bind (r := mmaEnable t en)
      intro enabled
      apply allOk_bind (r := zeroColumnMaskOk l g t none)
      intro zcm
      cases hB : TcShared.decode b.toNat with
      | none => trivial
      | some bDesc =>
        cases hDesc : TcMma.decode .one false .f16 i.toNat with
        | none => trivial
        | some desc =>
          simp only
          split
          · trivial
          · cases TcMma.makeOperands l (g/l.block) desc bDesc bDesc <;> simp only <;> trivial
    · simp only [hCount,↓reduceIte]
      trivial
  · simp only [hThread,↓reduceIte]
    trivial

private theorem firedTensorA {pc d : Nat} {tm : Tmpl} {o : Option TState}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : hasTensorA tm) (hf : Fires pc tm ⟨pc,.tc (.mma d op accum mask)⟩ o) :
    op.aTmem.isSome = true := by
  cases tm <;> simp only [hasTensorA] at h
  case tc k _ =>
    cases k <;> try contradiction
    cases congrArg Event.kind hf.1
    exact h
  case ub =>
    cases congrArg Event.kind hf.1

/-- The A operand of every actual PV fragment is in Tensor Memory, including loop revisits. -/
theorem PvInstruction.tensorA {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hIssue : PvInstruction X issue block step d op accum mask) :
    op.aTmem.isSome = true := by
  rcases get_source hX hIssue.decoded with ⟨_,hFault⟩ | ⟨_,_,_,_,hCode,hFires⟩
  · cases hFault
  rw [pvCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  exact firedTensorA tmemTemplateHasTensorA hFires

/-- A shared operand in a real PV issue is necessarily its B operand. -/
theorem PvInstruction.sharedOperandB {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {block : Fin 4} {step : Fin 8} {d index : Nat} {op : TcMma.OperandSpec}
    {isB accum : Bool} {mask : List Nat} {loc : Loc}
    (hIssue : PvInstruction X issue block step d op accum mask)
    (hByte : op.byteLoc (if isB then .b else .a) index = some loc) : isB = true := by
  cases isB
  · simp [TcMma.OperandSpec.byteLoc,hIssue.tensorA hX] at hByte
  · rfl

/-- Every actual shared A byte lies in the query banks, including pending or repeated issues. -/
theorem mmaSharedAByteRange {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {index : Nat} {loc : Loc} (h : X.MmaFootprint i false index loc) :
    Mma.SharedOperandRange l i.1 loc := by
  obtain ⟨_,d,op,accum,mask,hIssue,hLoc⟩ := mmaSharedFootprintIssue hX h
  rcases actualMmaInstruction hX hIssue with ⟨_,_,hQ⟩ | ⟨_,_,hPv⟩
  · exact hQ.queryByteRange hp hX hLoc
  · exact Bool.noConfusion (hPv.sharedOperandB hX (isB := false) hLoc)

end
end PTX.Kernels.TmlFa4Fwd.Thread
