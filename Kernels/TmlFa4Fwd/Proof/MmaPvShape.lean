-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvIssue
public import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
import Lemmas.Flow.TcTmpl
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- Runtime instruction shape and CTA affiliation for the transposed value operand. -/
def PvShape (l : Launch) (g : Nat) (op : TcMma.OperandSpec) : Prop :=
  op.descriptor = pvDescriptor ∧ op.lowCta = g/l.block ∧ op.highCta = g/l.block

private def templatePvShape (l : Launch) (g : Nat) : Tmpl → Prop
  | .tc (.mma _ op _ _) _ => PvShape l g op
  | .ub _ => True
  | _ => False

private theorem ofExecPvShape {l : Launch} {g : Nat} {r : Exec Tmpl}
    (h : AllOk (templatePvShape l g) r) : templatePvShape l g (ofExec r) := by
  cases r
  · trivial
  · exact h

private theorem execBindOk {α β : Type} (a : α) (f : α → Exec β) :
    (Except.ok a : Exec α) >>= f = f a := rfl

private theorem templateHasPvShape {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g d ta id : Nat} {s : TState} {off : Int} {bd en : Opnd}
    (hg : g < l.threads) (hr : s.regs id = some (b32 0x8210490)) :
    templatePvShape l g (eventTmpl Assumptions.all l g s
      (.tcMma (.dense .one false .f16 d (.tmem ta off) bd (.reg id)
        (List.replicate 4 (.imm 0)) en))) := by
  have hId := readBits_b32 (L := l) (g := g) hr (by decide : 0x8210490 < 2^32)
  have hNat : (BitVec.ofNat 64 0x8210490).toNat = 0x8210490 := rfl
  simp only [eventTmpl,tcTmpl_tcMma_tmem (.inr (.inl rfl)),mmaTmemTmpl,hg,↓reduceIte]
  apply ofExecPvShape
  apply allOk_bind
  intro dst
  apply allOk_bind
  intro a
  apply allOk_bind (r := tmemOffset a.toNat off)
  intro offset
  apply allOk_bind (r := readBits l g s 64 bd)
  intro b
  rw [hId]
  simp only [execBindOk,List.length_replicate,CtaGroup.size,Nat.reduceMul,↓reduceIte]
  apply allOk_bind (r := (List.replicate 4 (.imm 0 : Opnd)).mapM (readBits l g s 32))
  intro masks
  apply allOk_bind (r := mmaEnable s en)
  intro enabled
  apply allOk_bind (r := zeroColumnMaskOk l g s none)
  intro zcm
  cases hB : TcShared.decode b.toNat with
  | none => trivial
  | some dB =>
    simp only
    rw [hNat,pvDescriptor_decode]
    simp [pvDescriptor,TcMma.makeOperands,singleCtaGroup hp hg,
      pure,Except.pure,AllOk,PvShape,templatePvShape]

private theorem firesPvShape {l : Launch} {g pc d : Nat} {tm : Tmpl} {o : Option TState}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : templatePvShape l g tm) (hf : Fires pc tm ⟨pc,.tc (.mma d op accum mask)⟩ o) :
    PvShape l g op := by
  cases tm <;> simp only [templatePvShape] at h
  case tc k _ =>
    cases k <;> try contradiction
    cases congrArg Event.kind hf.1
    exact h
  case ub => cases congrArg Event.kind hf.1

/-- A PV contraction with the kernel's decoded ID has the fixed shape and same-CTA operands. -/
theorem pvIssueShapeOfId {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g d : Nat} {block : Fin 4} {step : Fin 8} {s u : TState}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hg : g < l.threads) (hId : s.regs (pvSite block).id = some (b32 0x8210490))
    (he : EStep kernel Assumptions.all l g s
      ⟨pvPc block step,.tc (.mma d op accum mask)⟩ (some u)) :
    PvShape l g op := by
  obtain ⟨ins,hGet,_,hFires⟩ := estep_event_source he
  have hPc := (estep_source_pc he).symm
  rw [hPc,pvCode block step] at hGet
  obtain rfl := Option.some.inj hGet
  rw [hPc] at hFires
  exact firesPvShape (templateHasPvShape hp hg hId) hFires

end
end PTX.Kernels.TmlFa4Fwd.Mma
