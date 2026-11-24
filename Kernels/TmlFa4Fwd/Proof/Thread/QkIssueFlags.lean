-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Lemmas.Flow.Final
import Lemmas.Flow.Tc
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Assumption PTX.Proof PTX.EventFrame _root_.PTX.Kernels.TmlFa4Fwd.Mma

private def qkIssueFields (step : Fin 8) (dst : Option Nat) : Tmpl → Prop
  | .tc (.mma d op accum mask) _ =>
    (∀ col ∈ dst, d = col) ∧ accum = decide (step.val ≠ 0) ∧
      mask = List.replicate 4 0 ∧ op.collector = {}
  | .ub _ => True
  | _ => False

private theorem qkIssueFieldsOfExec {step : Fin 8} {dst : Option Nat} {e : Exec Tmpl}
    (h : AllOk (qkIssueFields step dst) e) : qkIssueFields step dst (ofExec e) := by
  cases e
  · trivial
  · exact h

private theorem bindOk {α β : Type} (v : α) (f : α → Exec β) :
    (Except.ok v : Exec α) >>= f = f v := rfl

private theorem qkTemplateFields {l : Launch} {g : Nat} {t : TState}
    (block : Fin 4) (step : Fin 8) {dst : Option Nat}
    (hD : ∀ d ∈ dst, t.regs (qkDestination block) = some (b32 d) ∧ d < 2^32) :
    qkIssueFields step dst (eventTmpl Assumptions.all l g t
      (.tcMma (.dense .one false .f16 (qkDestination block) (.smem (.reg (9624 + step.val)))
        (.reg (qkBReg block + step.val)) (.reg 9632) (List.replicate 4 (.imm 0))
        (.imm (if step.val = 0 then 0 else 1))))) := by
  simp only [eventTmpl,tcTmpl_tcMma_smem (.inr (.inl rfl)),mmaSmemTmpl]
  apply qkIssueFieldsOfExec
  by_cases hg : g < l.threads
  · simp only [hg,↓reduceIte]
    cases hd : readBits l g t 32 (.reg (qkDestination block)) with
    | error => trivial
    | ok d =>
      simp only [bindOk]
      apply allOk_bind (r := readBits l g t 64 (.reg (9624 + step.val)))
      intro a
      apply allOk_bind (r := readBits l g t 64 (.reg (qkBReg block + step.val)))
      intro b
      apply allOk_bind (r := readBits l g t 32 (.reg 9632))
      intro i
      have hMasks : (List.replicate 4 (.imm 0)).mapM (readBits l g t 32) =
          .ok (List.replicate 4 (BitVec.ofNat 64 0)) := rfl
      have hEnable : mmaEnable t (.imm (if step.val = 0 then 0 else 1)) =
          .ok (decide (step.val ≠ 0)) := by
        by_cases h : step.val = 0 <;> simp [mmaEnable,h,pure,Except.pure]
      simp only [hMasks,List.length_replicate,show 4 * CtaGroup.one.size = 4 from rfl,
        ↓reduceIte,hEnable,bindOk,zeroColumnMaskOk,pure,Except.pure]
      cases TcShared.decode a.toNat <;> try trivial
      case some da =>
        cases TcShared.decode b.toNat <;> try trivial
        case some db =>
          cases TcMma.decode .one false .f16 i.toNat <;> try trivial
          case some desc =>
            cases hOp : TcMma.makeOperands l (g / l.block) desc da db
            · simp only [hOp]
              trivial
            · simp only [hOp,AllOk,qkIssueFields,List.map_replicate]
              refine ⟨?_,True.intro,rfl,True.intro⟩
              intro col hc
              obtain ⟨hReg,hBound⟩ := hD col hc
              rw [readBits_b32 hReg hBound] at hd
              obtain rfl := Except.ok.inj hd
              exact toNat_ofNat_lt (by omega)
  · simp only [hg,↓reduceIte]
    trivial

private theorem qkStepAllFields {l : Launch} {g : Nat} {t u : TState} (block : Fin 4) (step : Fin 8)
    {dst : Option Nat} (hD : ∀ col ∈ dst, t.regs (qkDestination block) = some (b32 col) ∧
      col < 2^32) {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (he : EStep kernel Assumptions.all l g t
      ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩ (some u)) :
    (∀ col ∈ dst, d = col) ∧ accum = decide (step.val ≠ 0) ∧
      mask = List.replicate 4 0 ∧ op.collector = {} := by
  have hPc := estep_source_pc he
  obtain ⟨i,hCode,_,hFires⟩ := estep_event_source he
  rw [← hPc,qkCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  have hm := qkTemplateFields (l := l) (g := g) block step hD
  generalize ht : eventTmpl Assumptions.all l g t _ = tm at hm hFires
  cases tm <;> simp only [qkIssueFields] at hm
  case tc k _ =>
    cases k <;> try contradiction
    cases congrArg Event.kind hFires.1
    exact hm
  case ub => cases hFires.2

/-- The real QK event decodes the clear/accumulate flag and four zero lane masks.
A destination register fact also resolves the column address. -/
theorem qkStepFields {l : Launch} {g : Nat} {t u : TState} (block : Fin 4) (step : Fin 8)
    {dst : Option Nat} (hD : ∀ col ∈ dst, t.regs (qkDestination block) = some (b32 col) ∧
      col < 2^32) {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (he : EStep kernel Assumptions.all l g t
      ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩ (some u)) :
    (∀ col ∈ dst, d = col) ∧ accum = decide (step.val ≠ 0) ∧ mask = List.replicate 4 0 := by

  obtain ⟨hAddr,hAcc,hMask,_⟩ := qkStepAllFields block step hD he
  exact ⟨hAddr,hAcc,hMask⟩

variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {block : Fin 4} {frag : Fin 8} {d : Nat} {s : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat}
include hX

private theorem QkInstruction.issueAllFlags (hi : QkInstruction X i block frag d s accum mask) :
    accum = decide (frag.val ≠ 0) ∧
      mask = List.replicate 4 0 ∧ s.collector = {} := by
  have he := hi.decoded
  obtain ⟨_,hr⟩ := hX.thr i.1 (event_thread_lt hX he)
  obtain ⟨_,o,_,hStep⟩ := hr.before_event he
  cases o with
  | none =>
    obtain ⟨_,_,hf⟩ := hStep
    rcases PTX.Flow.fires_none_ends hf with ⟨_,h⟩ | h <;> cases h
  | some u =>
    exact (qkStepAllFields block frag (dst := none) (by simp) hStep).2

/-- Any actual QK fragment's flags are fixed by its fragment number. -/
theorem QkInstruction.issueFlags (hi : QkInstruction X i block frag d s accum mask) :
    accum = decide (frag.val ≠ 0) ∧ mask = List.replicate 4 0 := by

  exact ⟨(hi.issueAllFlags hX).1,(hi.issueAllFlags hX).2.1⟩

/-- No QK fragment requests a Tensor Core operand collector. -/
theorem QkInstruction.issueCollector (hi : QkInstruction X i block frag d s accum mask) :
    s.collector = {} :=
  (hi.issueAllFlags hX).2.2

end PTX.Kernels.TmlFa4Fwd.Thread
