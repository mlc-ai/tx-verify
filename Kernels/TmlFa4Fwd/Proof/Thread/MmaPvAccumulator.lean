-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Lemmas.Flow.TcMmaTs
import Lemmas.Flow.TcTmpl
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

private def templateAccumulation (accum : Bool) : Tmpl → Prop
  | .tc (.mma _ _ flag _) _ => flag = accum
  | .ub _ => True
  | _ => False

private theorem templateReadsAccumulation {l : Launch} {g d ta rb ri : Nat}
    {s : TState} {off : Int} {en : Opnd} {accum : Bool}
    (hg : g < l.threads) (hen : mmaEnable s en = .ok accum) :
    templateAccumulation accum (eventTmpl Assumptions.all l g s
      (.tcMma (.dense .one false .f16 d (.tmem ta off) (.reg rb) (.reg ri)
        (List.replicate 4 (.imm 0)) en))) := by
  have hExec {r : Exec Tmpl} (h : AllOk (templateAccumulation accum) r) :
      templateAccumulation accum (ofExec r) := by
    cases r
    · trivial
    · exact h
  simp only [eventTmpl,tcTmpl_tcMma_tmem (.inr (.inl rfl)),mmaTmemTmpl,hg,↓reduceIte]
  apply hExec
  apply allOk_bind (r := readBits l g s 32 (.reg d))
  intro dst
  apply allOk_bind (r := readBits l g s 32 (.reg ta))
  intro a
  apply allOk_bind (r := tmemOffset a.toNat off)
  intro tmem
  apply allOk_bind (r := readBits l g s 64 (.reg rb))
  intro b
  apply allOk_bind (r := readBits l g s 32 (.reg ri))
  intro id
  simp only [List.length_replicate,CtaGroup.size,Nat.reduceMul,↓reduceIte]
  apply allOk_bind (r := (List.replicate 4 (.imm 0 : Opnd)).mapM (readBits l g s 32))
  intro masks
  rw [hen]
  have hBind {α β : Type} (a : α) (f : α → Exec β) :
      (Except.ok a : Exec α) >>= f = f a := rfl
  simp only [hBind]
  apply allOk_bind (r := zeroColumnMaskOk l g s none)
  intro zcm
  cases TcShared.decode b.toNat with
  | none => trivial
  | some dB =>
    cases TcMma.decode .one false .f16 id.toNat with
    | none => trivial
    | some desc =>
      simp only
      split
      · trivial
      · cases TcMma.makeOperands l (g/l.block) desc dB dB <;> simp only <;> trivial

private theorem firedAccumulation {pc d : Nat} {t : Tmpl} {u : Option TState}
    {op : TcMma.OperandSpec} {accum flag : Bool} {mask : List Nat}
    (h : templateAccumulation accum t) (hf : Fires pc t ⟨pc,.tc (.mma d op flag mask)⟩ u) :
    flag = accum := by
  cases t <;> simp only [templateAccumulation] at h
  case tc k _ =>
    cases k <;> try contradiction
    cases congrArg Event.kind hf.1
    exact h
  case ub => cases congrArg Event.kind hf.1

/-- The actual PV event uses the flag read by its decoded accumulator operand. -/
theorem pvAccumulationAtEvent {l : Launch} {g : Nat} (hg : g < l.threads)
    (block : Fin 4) (step : Fin 8) {t : TState} {u : Option TState} {d : Nat}
    {op : TcMma.OperandSpec} {accum flag : Bool} {mask : List Nat}
    (hEnable : mmaEnable t (pvEnable block step) = .ok accum)
    (hStep : EStep kernel Assumptions.all l g t
      ⟨pvPc block step,.tc (.mma d op flag mask)⟩ u) : flag = accum := by
  have hPc := (estep_source_pc hStep).symm
  obtain ⟨ins,hCode,hFires⟩ := mmaRoleEventSource hStep (by intro f h; contradiction)
  change t.pc = pvPc block step at hPc
  rw [hPc,pvCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  rw [hPc] at hFires
  exact firedAccumulation (templateReadsAccumulation hg hEnable) hFires

/-- Every fragment after the first adds into the existing output accumulator, in every visit. -/
theorem PvInstruction.accumulatesAfterFirstFragment {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hIssue : PvInstruction X issue block step d op accum mask)
    (hStep : step.val ≠ 0) : accum = true := by
  obtain ⟨_,t,u,_,he⟩ := hIssue.valueWordAtIssue hp hX
  exact pvAccumulationAtEvent (event_thread_lt hX hIssue.decoded) block step
    (by simp [pvEnable,hStep,mmaEnable,pure,Except.pure]) he

end PTX.Kernels.TmlFa4Fwd.Thread
