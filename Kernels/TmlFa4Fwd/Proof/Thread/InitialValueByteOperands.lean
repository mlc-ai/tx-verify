-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValuePhase
public import Kernels.TmlFa4Fwd.Proof.MmaPvInputLayout
import Kernels.TmlFa4Fwd.Proof.MmaValueInstructionFrame
import Lemmas.Flow.Final
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma (kvStart pvCode
  pvEnable pvFragment pvOperands pvPc pvSite qkByteIndex sharedDescriptor singleCtaGroup
  valueInstructionFrame)

noncomputable section

private def valueLayout (cta : Nat) : Tmpl → Prop
  | .tc (.mma _ op _ _) _ => op.descriptor = pvDescriptor ∧
      op.lowCta = cta ∧ op.highCta = cta
  | .ub _ => True
  | _ => False

private theorem valueLayoutOfExec {cta : Nat} {r : Exec Tmpl} (h : AllOk (valueLayout cta) r) :
    valueLayout cta (ofExec r) := by
  cases r
  · trivial
  · exact h

private theorem execBindOk {α β : Type} (a : α) (f : α → Exec β) :
    (Except.ok a : Exec α) >>= f = f a := rfl

private theorem valueTemplateHasLayout {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {t : TState} (hg : g < l.threads)
    (block : Fin 4) (frag : Fin 8) (hId : t.regs (pvSite block).id = some (b32 0x8210490)) :
    valueLayout (g/l.block) (eventTmpl Assumptions.all l g t
      (.tcMma (.dense .one false .f16 (pvSite block).dst
        (.tmem (pvSite block).a (8*(frag.val : Int))) (.reg (pvSite block).b)
        (.reg (pvSite block).id) (List.replicate 4 (.imm 0)) (pvEnable block frag)))) := by
  simp only [eventTmpl,tcTmpl_tcMma_tmem (.inr (.inl rfl)),mmaTmemTmpl]
  apply valueLayoutOfExec
  have hNat : (BitVec.ofNat 64 0x8210490).toNat = 0x8210490 := rfl
  simp only [readBits_b32 (L := l) (g := g) hId (by decide),execBindOk,hNat,pvDescriptor_decode]
  have hCount : (List.replicate 4 (.imm 0 : Opnd)).length = 4 * CtaGroup.one.size := rfl
  have hTranspose : pvDescriptor.transposeA ≠ true := by decide
  simp only [hg,hCount,hTranspose,Bool.false_eq_true,↓reduceIte]
  apply allOk_bind
  intro d
  apply allOk_bind
  intro ta
  generalize tmemOffset ta.toNat (8*(frag.val : Int)) = offset
  cases offset with
  | error => trivial
  | ok a =>
    simp only [execBindOk]
    apply allOk_bind (r := readBits l g t 64 (.reg (pvSite block).b))
    intro b
    apply allOk_bind (r := (List.replicate 4 (.imm 0)).mapM (readBits l g t 32))
    intro masks
    apply allOk_bind (r := mmaEnable t (pvEnable block frag))
    intro accum
    apply allOk_bind (r := zeroColumnMaskOk l g t none)
    intro z
    cases hDec : TcShared.decode b.toNat with
    | none => trivial
    | some db =>
      have hAssembly : TcMma.makeOperands l (g/l.block) pvDescriptor db db =
          some ⟨pvDescriptor,db,db,g/l.block,g/l.block,none,{}⟩ := by
        simp [TcMma.makeOperands,singleCtaGroup hp hg,pvDescriptor]
      simp only [hAssembly]
      exact ⟨rfl,rfl,rfl⟩

private theorem valueLayoutFires {pc cta dst : Nat} {s : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} {tmpl : Tmpl} {u : TState}
    (h : valueLayout cta tmpl) (hf : Fires pc tmpl ⟨pc,.tc (.mma dst s accum mask)⟩ (some u)) :
    s.descriptor = pvDescriptor ∧ s.lowCta = cta ∧ s.highCta = cta := by
  cases tmpl <;> simp only [valueLayout] at h
  case tc k _ =>
    cases k <;> try contradiction
    have he := congrArg Event.kind hf.1
    cases he
    exact h
  case ub => cases hf.2

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {issue : EvId} {steady : Bool} {stage : Fin 2}
    {frag : Fin 8} {dst : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (he : InitialValueFragment X issue steady stage frag dst op accum mask)
include hp hX he

/-- The actual PV B operand has the decoded instruction layout and issuer CTA. -/
theorem InitialValueFragment.valueLayout :
    op.descriptor = pvDescriptor ∧ op.lowCta = issue.1/l.block ∧ op.highCta = issue.1/l.block := by
  let block := firstPvBlock steady stage
  have he' : X.get issue = some ⟨pvPc block frag,.tc (.mma dst op accum mask)⟩ := he
  obtain ⟨s,o,hId,hE⟩ := valueInstructionFrame hp hX block frag he'
  have hStep : ∃ u, EStep kernel Assumptions.all l issue.1 s
      ⟨pvPc block frag,.tc (.mma dst op accum mask)⟩ (some u) := by
    cases o with
    | some u => exact ⟨u,hE⟩
    | none =>
      obtain ⟨tm,_,hFires⟩ := hE
      rcases fires_none_ends hFires with ⟨f,hBad⟩ | hBad <;> cases hBad
  obtain ⟨u,hReturn⟩ := hStep
  obtain ⟨i,hCode,_,hFires⟩ := estep_event_source hReturn
  have hPc : s.pc = pvPc block frag := (estep_source_pc hReturn).symm
  rw [hPc,pvCode block frag] at hCode
  obtain rfl := Option.some.inj hCode
  rw [hPc] at hFires
  exact valueLayoutFires (valueTemplateHasLayout hp (event_thread_lt hX he') block frag hId)
    hFires

/-- The concrete B descriptor of an actual initial value fragment agrees with
the packet geometry for every byte index. -/
theorem InitialValueFragment.valueByteLoc
    (hB : op.b = sharedDescriptor (kvStart l 1 + pvFragment frag) 16384) (index : Nat) :
    op.byteLoc .b index =
      (pvOperands l issue.1 (firstPvBlock steady stage) frag 1).byteLoc .b index := by
  obtain ⟨hDesc,hLow,hHigh⟩ := he.valueLayout hp hX
  simp only [TcMma.OperandSpec.byteLoc,pvOperands,hDesc,hLow,hHigh,hB,reduceCtorEq,false_and,
    ↓reduceIte]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Thread
