-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQueryCoverage
import Lemmas.Execution.EventFrameBase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private def qkOperandTemplate (l : Launch) (g : Nat) (t : TState) (block : Fin 4)
    (step : Fin 8) : Tmpl :=
  mmaSmemTmpl l g t .one false .f16 (qkDestination block) (.reg (9624 + step.val))
    (.reg (qkBReg block + step.val)) (.reg 9632) (List.replicate 4 (.imm 0))
    (.imm (if step.val = 0 then 0 else 1)) none {}

private def QkOperandResult (l : Launch) (g : Nat) (t : TState) (block : Fin 4) (step : Fin 8)
    (tmpl : Tmpl) : Prop :=
  ∃ d op accum mask, tmpl = .tc (.mma d op accum mask) (next t) ∧
    QueryOperandFragment l g (qkStage block) step op

private theorem okBind {α β : Type} (a : α) (f : α → Exec β) :
    (Except.ok a >>= f) = f a := rfl

private theorem execQkOperand {l : Launch} {g : Nat} {t : TState} {block : Fin 4} {step : Fin 8}
    {r : Exec Tmpl} (h : AllOk (QkOperandResult l g t block step) r) :
    (∃ f, ofExec r = .ub f) ∨ QkOperandResult l g t block step (ofExec r) := by
  cases r with
  | error fault => exact .inl ⟨fault, rfl⟩
  | ok m => exact .inr h

private theorem decodedQkOperand {l : Launch} {g : Nat} {t : TState} (block : Fin 4) (step : Fin 8)
    (qword iword : BitVec 64) (hg : g < l.threads)
    (hA : readBits l g t 64 (.reg (9624 + step.val)) = .ok qword)
    (hADecode : TcShared.decode qword.toNat =
      some (sharedDescriptor (qStart l (qkStage block) + qkFragment step) 16))
    (hId : readBits l g t 32 (.reg 9632) = .ok iword)
    (hIdDecode : TcMma.decode .one false .f16 iword.toNat = some qkDescriptor)
    (hGroup : l.ctaGroup (g / l.block) qkDescriptor.group = some [g / l.block]) :
    (∃ f, qkOperandTemplate l g t block step = .ub f) ∨
      QkOperandResult l g t block step (qkOperandTemplate l g t block step) := by
  have hMask : (List.replicate 4 (.imm 0)).mapM (readBits l g t 32) =
      .ok (List.replicate 4 (0 : BitVec 64)) := rfl
  have hEnable : mmaEnable t (.imm (if step.val = 0 then 0 else 1)) =
      .ok (decide (step.val ≠ 0)) := by
    by_cases h : step.val = 0
    · rw [ite_eq_left h, decide_eq_false (by intro hne; exact hne h)]
      rfl
    · rw [ite_eq_right h, decide_eq_true h]
      rfl
  unfold qkOperandTemplate mmaSmemTmpl
  apply execQkOperand
  simp only [hg, ↓reduceIte, pure_bind, hA, hId, hMask, hEnable, zeroColumnMaskOk, okBind,
    List.length_replicate, CtaGroup.size, Nat.reduceMul]
  apply allOk_bind
  intro d
  apply allOk_bind
  intro bw
  simp only [hADecode, hIdDecode]
  rcases Option.eq_none_or_eq_some (TcShared.decode bw.toNat) with hB | ⟨bd, hB⟩
  · rw [hB]
    exact trivial
  · simp only [hB]
    let op : TcMma.OperandSpec := ⟨qkDescriptor,
      sharedDescriptor (qStart l (qkStage block) + qkFragment step) 16,
      bd, g / l.block, g / l.block, none, {}⟩
    have hMake : TcMma.makeOperands l (g / l.block) qkDescriptor
        (sharedDescriptor (qStart l (qkStage block) + qkFragment step) 16) bd = some op := by
      unfold TcMma.makeOperands
      rw [hGroup]
      rfl
    simp only [hMake]
    exact ⟨d.toNat, op, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {p : Params}

/-- A returning QK event decodes the prepared A fragment independently of values in the
score accumulator or the K descriptor. The result retains the actual issued operands. -/
theorem observedQkOperand {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} (hg : g < l.threads)
    (block : Fin 4) (step : Fin 8) {t u : TState} {e : Event} (ht : t.pc = qkPc block + step.val)
    (hA : t.regs (9624 + step.val) = some
      (b64 (sharedDescriptorWord (qStart l (qkStage block) + qkFragment step) 16)))
    (hId : t.regs 9632 = some (b32 0x8200490))
    (hStep : EStep kernel Assumptions.all l g t e (some u)) :
    ∃ d op accum mask, e = ⟨qkPc block + step.val, .tc (.mma d op accum mask)⟩ ∧
      QueryOperandFragment l g (qkStage block) step op ∧ u = next t := by
  let base := qStart l (qkStage block) + qkFragment step
  have hBase : base < 2 ^ 18 ∧ base % 16 = 0 := by
    have hShared := hp.shared.2.1
    have hAlign := hp.shared.1
    have hi := (qkStage block).isLt
    have hFrag := step.isLt
    dsimp [base, qStart, qkFragment]
    omega
  have hWord := sharedDescriptorWord_lt hBase.1 hBase.2 (.inl rfl)
  have hReadA := readBits_b64 (L := l) (g := g) hA hWord
  have hDecodeA : TcShared.decode (BitVec.ofNat 64 (sharedDescriptorWord base 16)).toNat =
      some (sharedDescriptor base 16) := by
    rw [toNat_ofNat_lt hWord]
    exact sharedDescriptor_decode hBase.1 hBase.2 (.inl rfl)
  have hReadId := readBits_b32 (L := l) (g := g) hId (by decide)
  have hDecodeId : TcMma.decode .one false .f16 (0x8200490#64).toNat = some qkDescriptor :=
    qkDescriptor_decode
  have hGroup : l.ctaGroup (g / l.block) qkDescriptor.group = some [g / l.block] := by
    rw [show qkDescriptor.group = .one from rfl]
    exact singleCtaGroup hp hg
  have hResult := decodedQkOperand block step _ _ hg hReadA hDecodeA hReadId hDecodeId hGroup
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source hStep
  rw [ht, qkCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  change Fires t.pc (qkOperandTemplate l g t block step) e (some u) at hFire
  rcases hResult with ⟨fault, hFault⟩ | ⟨d, op, accum, mask, hTemplate, hOperand⟩
  · rw [hFault] at hFire
    cases hFire.2
  · rw [hTemplate] at hFire
    have hEvent := hFire.1
    rw [ht] at hEvent
    exact ⟨d, op, accum, mask, hEvent, hOperand, Option.some.inj hFire.2⟩

private theorem queryBankOperandWalk {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat}
    (hg : g < l.threads) (block : Fin 4) (n start : Nat) (hBounds : start + n ≤ 8) {s : TState}
    {events : List Event} {visits : List Visit} (hs : At s (qkPc block + start) [])
    (hGuard : s.regs (qkGuard block) = some (.pred true)) (hId : s.regs 9632 = some (b32 0x8200490))
    (hA : ∀ step : Fin 8, s.regs (9624 + step.val) = some
      (b64 (sharedDescriptorWord (qStart l (qkStage block) + qkFragment step) 16)))
    (hWalk : Walk kernel Assumptions.all l g s events visits) {index : Nat} {target : Event}
    (hGet : events[index]? = some target) (hTarget : qkPc block + 8 ≤ target.pc) :
    n ≤ index ∧
      ∀ j (hj : j < n), ∃ d op accum mask,
        events[j]? = some ⟨qkPc block + start + j, .tc (.mma d op accum mask)⟩ ∧
        QueryOperandFragment l g (qkStage block) ⟨start + j, by omega⟩ op := by
  induction n generalizing start s events visits index with
  | zero => exact ⟨by omega, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
  | succ n ih =>
    let step : Fin 8 := ⟨start, by omega⟩
    have hCode := congrArg (fun i => kernel.code[i]?) hs.1
    rw [show qkPc block + start = qkPc block + step.val from rfl, qkCode block step] at hCode
    have hPred : guardHolds s (some (qkGuard block, false)) = .ok true := by
      simp [guardHolds, readReg, hGuard, bind, Except.bind, pure, Except.pure]
    have hOut := out_event (A := Assumptions.all) (L := l) (g := g)
      hs.2.2.2.1 hCode hPred rfl
    cases hWalk with
    | stop => simp at hGet
    | tau h _ => rw [Tau, hOut] at h; cases h
    | last h =>
      have hEq := List.mem_singleton.mp (List.mem_of_getElem? hGet)
      have hPc := (congrArg Event.pc hEq).trans (estep_source_pc h)
      have hPos := hs.1
      omega
    | @ev _ u e tail trail h hWalk =>
      obtain ⟨d, op, accum, mask, hEvent, hOperand, rfl⟩ :=
        observedQkOperand hp hg block step hs.1 (hA step) hId h
      cases index with
      | zero =>
        have hEq := Option.some.inj hGet
        have hPc := congrArg Event.pc (hEq.symm.trans hEvent)
        change target.pc = qkPc block + start at hPc
        omega
      | succ index =>
        have hTail : tail[index]? = some target := hGet
        have hNext : At (next s) (qkPc block + (start + 1)) [] := by
          simpa only [Nat.add_assoc] using hs.next
        obtain ⟨hIndex, hRest⟩ := ih (start + 1) (by omega) hNext hGuard hId hA hWalk hTail
        refine ⟨by omega, ?_⟩
        intro j hj
        cases j with
        | zero => exact ⟨d, op, accum, mask, congrArg some hEvent, hOperand⟩
        | succ j =>
          obtain ⟨d, op, accum, mask, hLater, hOp⟩ := hRest j (by omega)
          have hSum : start + 1 + j = start + (j + 1) := by omega
          have hPc : qkPc block + (start + 1) + j = qkPc block + start + (j + 1) := by omega
          exact ⟨d, op, accum, mask, by simpa only [List.getElem?_cons_succ, hPc] using hLater,
            by simpa only [hSum] using hOp⟩

/-- Once the actual elected lane has prepared the Q descriptor bank, its next eight real
fragment issues precede any recorded event past the bank. The trace may end at that later event. -/
theorem queryBankOperandsBeforeEvent {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (block : Fin 4) {g pos index : Nat} {s : TState}
    {visits : List Visit} {target : Event} (hs : At s (qkPc block) [])
    (hGuard : s.regs (qkGuard block) = some (.pred true)) (hId : s.regs 9632 = some (b32 0x8200490))
    (hA : ∀ step : Fin 8, s.regs (9624 + step.val) = some
      (b64 (sharedDescriptorWord (qStart l (qkStage block) + qkFragment step) 16)))
    (hWalk : Walk kernel Assumptions.all l g s ((X.tr g).drop pos) visits) (hPos : pos ≤ index)
    (hTarget : X.get (g, index) = some target) (hAfter : qkPc block + 8 ≤ target.pc) :
    ∀ step : Fin 8, ∃ d op accum mask,
      pos + step.val < index ∧
      X.get (g, pos + step.val) = some ⟨qkPc block + step.val, .tc (.mma d op accum mask)⟩ ∧
      QueryOperandFragment l g (qkStage block) step op := by
  have hGet : ((X.tr g).drop pos)[index - pos]? = some target := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hPos]
  obtain ⟨hIndex, hBank⟩ := queryBankOperandWalk hp (event_thread_lt hX hTarget) block
    8 0 (by decide) (by simpa using hs) hGuard hId hA hWalk hGet hAfter
  intro step
  obtain ⟨d, op, accum, mask, hRead, hOp⟩ := hBank step.val step.isLt
  refine ⟨d, op, accum, mask, by have := step.isLt; omega, ?_, ?_⟩
  · simpa only [Execution.get, List.getElem?_drop, Nat.add_zero] using hRead
  · simpa only [Nat.zero_add, Fin.eta] using hOp

end
end PTX.Kernels.TmlFa4Fwd.Mma
