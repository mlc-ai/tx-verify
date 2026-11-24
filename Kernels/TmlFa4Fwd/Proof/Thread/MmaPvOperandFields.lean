-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailDestination
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma

private def fixedFields (continuation : TState) : Tmpl → Prop
  | .tc (.mma _ op _ mask) u => op.a = op.b ∧ op.collector = {} ∧
    mask = List.replicate 4 0 ∧ u = continuation
  | .ub _ => True
  | _ => False

private theorem identicalDescriptors {l : Launch} {cta : Nat} {desc : TcMma.Descriptor}
    {b : TcShared.Descriptor} {op : TcMma.OperandSpec}
    (h : TcMma.makeOperands l cta desc b b = some op) : op.a = op.b := by
  unfold TcMma.makeOperands at h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  rfl

set_option maxRecDepth 100000 in
private theorem templateFields {l : Launch} {g : Nat} {t : TState}
    (block : Fin 4) (step : Fin 8) (hg : g < l.threads) :
    let site := pvSite block
    fixedFields (next t) (eventTmpl Assumptions.all l g t
      (.tcMma (.dense .one false .f16 site.dst (.tmem site.a (8*(step.val : Int)))
        (.reg site.b) (.reg site.id) (List.replicate 4 (.imm 0)) (pvEnable block step)))) := by
  dsimp only
  have hExec {r : Exec Tmpl} (h : AllOk (fixedFields (next t)) r) :
      fixedFields (next t) (ofExec r) := by
    cases r
    · trivial
    · exact h
  have hBind {α β : Type} (a : α) (f : α → Exec β) :
      (Except.ok a : Exec α) >>= f = f a := rfl
  have hMasks : (List.replicate 4 (.imm 0)).mapM (readBits l g t 32) =
      .ok (List.replicate 4 (BitVec.ofNat 64 0)) := rfl
  simp only [eventTmpl,tcTmpl_tcMma_tmem (.inr (.inl rfl)),mmaTmemTmpl,hg,↓reduceIte]
  apply hExec
  apply allOk_bind
  intro d
  apply allOk_bind (r := readBits l g t 32 (.reg (pvSite block).a))
  intro column
  generalize tmemOffset column.toNat (8*(step.val : Int)) = offset
  apply allOk_bind (r := offset)
  intro a
  apply allOk_bind (r := readBits l g t 64 (.reg (pvSite block).b))
  intro b
  apply allOk_bind (r := readBits l g t 32 (.reg (pvSite block).id))
  intro id
  simp only [hMasks,hBind,List.length_replicate,CtaGroup.size,Nat.reduceMul,↓reduceIte]
  apply allOk_bind (r := mmaEnable t (pvEnable block step))
  intro accum
  apply allOk_bind (r := zeroColumnMaskOk l g t none)
  intro zcm
  cases TcShared.decode b.toNat with
  | none => trivial
  | some b =>
    cases TcMma.decode .one false .f16 id.toNat with
    | none => trivial
    | some desc =>
      simp only
      split
      · trivial
      · cases hOp : TcMma.makeOperands l (g/l.block) desc b b with
        | none => trivial
        | some op =>
          simp only [AllOk,fixedFields,List.map_replicate]
          have hSame := identicalDescriptors hOp
          exact ⟨hSame,rfl,rfl,rfl⟩

private theorem firesFields {t : Tmpl} {u : Option TState} {s : TState} {pc d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hFields : fixedFields (next s) t)
    (hFires : Fires pc t ⟨pc,.tc (.mma d op accum mask)⟩ u) :
    op.a = op.b ∧ op.collector = {} ∧ mask = List.replicate 4 0 ∧ u = some (next s) := by
  cases t <;> simp only [fixedFields] at hFields
  case tc kind _ =>
    cases kind <;> try contradiction
    cases congrArg Event.kind hFires.1
    exact ⟨hFields.1,hFields.2.1,hFields.2.2.1,hFires.2.trans (congrArg some hFields.2.2.2)⟩
  case ub =>
    cases congrArg Event.kind hFires.1

/-- A real PV event returns to the next decoded instruction and supplies fixed fields. -/
theorem pvFieldsOfStep {l : Launch} {g : Nat} {t : TState} {u : Option TState}
    (hg : g < l.threads) (block : Fin 4) (step : Fin 8) {d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hStep : EStep kernel Assumptions.all l g t ⟨pvPc block step,.tc (.mma d op accum mask)⟩ u) :
    op.a = op.b ∧ op.collector = {} ∧ mask = List.replicate 4 0 ∧ u = some (next t) := by
  have hPc : t.pc = pvPc block step := (estep_source_pc hStep).symm
  obtain ⟨ins,hCode,hFires⟩ := mmaRoleEventSource hStep (by intro f h; contradiction)
  rw [hPc,pvCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  rw [hPc] at hFires
  exact firesFields (templateFields block step hg) hFires

/-- Every actual PV has its decoded zero lane masks and no collector modifier.
Its shared descriptor fields both name the V tile. -/
theorem PvInstruction.fixedOperandFields {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {block : Fin 4} {step : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : PvInstruction X i block step d op accum mask) :
    op.a = op.b ∧ op.collector = {} ∧ mask = List.replicate 4 0 := by
  have he := hIssue.decoded
  have hg := event_thread_lt hX he
  obtain ⟨_,hr⟩ := hX.thr i.1 hg
  obtain ⟨t,u,_,hStep⟩ := hr.before_event he
  have h := pvFieldsOfStep hg block step hStep
  exact ⟨h.1,h.2.1,h.2.2.1⟩

end PTX.Kernels.TmlFa4Fwd.Thread
