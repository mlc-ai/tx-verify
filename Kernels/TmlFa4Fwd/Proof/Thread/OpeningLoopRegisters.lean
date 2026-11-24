-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMassReach

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

noncomputable section

private def decisionScope (pc : Nat) : Bool :=
  (5006 ≤ pc && pc ≤ 5109) || (6654 ≤ pc && pc ≤ 6676) || (7605 ≤ pc && pc ≤ 7616)

private def decisionAudit (pc : Nat) (ins : Instr) : Bool :=
  (ins.guard.isNone || decisionScope (pc+1)) &&
  (!ins.op.isLocal ||
    (!(Assumptions.swExp2Sites.contains pc) &&
      [1062,2535,5127,7132,1230].all (fun n => !(writesRegs ins.op).contains n) &&
      decisionScope (nextPc ins.op pc) &&
      (match ins.op with | .brx .. => false | _ => true)))

private theorem decisionAuditAt {pc : Nat} {ins : Instr} (hPc : decisionScope pc = true)
    (hc : kernel.code[pc]? = some ins) : decisionAudit pc ins = true := by
  have hAll : ((kernel.code.zipIdx 0).filter (fun (_,i) => decisionScope i)).all
      (fun (ins,i) => decisionAudit i ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact List.all_eq_true.mp hAll (ins,pc)
    (List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr hc,hPc⟩)

private theorem decisionStep {l : Launch} {g : Nat} {s u : TState}
    (hPc : decisionScope s.pc = true) (hStep : Tau kernel Assumptions.all l g s u) :
    decisionScope u.pc = true ∧
      ∀ r ∈ [1062,2535,5127,7132,1230], u.regs r = s.regs r := by
  obtain ⟨ins,hCode,_,hOperation⟩ := tauScoreSource hStep
  have h := decisionAuditAt hPc hCode
  rcases hOperation with ⟨rfl,hGuard⟩ | ⟨_,hLoc,hExec⟩
  · refine ⟨?_,fun _ _ => rfl⟩
    cases hSome : ins.guard with
    | none => simp [hSome,guardHolds,pure,Except.pure] at hGuard
    | some v =>
      change decisionScope (s.pc+1) = true
      simp only [decisionAudit,hSome,Option.isNone_some,Bool.false_or,Bool.and_eq_true] at h
      exact h.1
  · simp only [decisionAudit,hLoc,Bool.not_true,Bool.false_or,Bool.and_eq_true,
      Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at h
    rcases scoreExecLocal hExec with hLocal | ⟨_,hSite,_,_⟩
    · have hNoBrx : ¬ BrxTarget ins.op u.pc := by
        cases hOp : ins.op <;> simp only [BrxTarget,not_false_eq_true]
        simp [hOp] at h
      exact ⟨(hLocal.pc.resolve_right hNoBrx).symm ▸ h.2.1.2,fun r hr =>
        hLocal.regs r (by
          simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using
            List.all_eq_true.mp h.2.1.1.2 r hr)⟩
    · exact (h.2.1.1.1 hSite).elim

/-- The local controls that seed or switch loops preserve the opening lane and ABI frame. -/
theorem openingLoopRegistersLocal {p : Params} {l : Launch} {g : Nat} {s u : TState}
    (hStart : s.pc = 5006 ∨ s.pc = 6654)
    (hFrame : Holds s.regs (openingDenominatorRegisters p l g))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    Holds u.regs (openingDenominatorRegisters p l g) := by
  have hs : decisionScope s.pc = true := by rcases hStart with h | h <;> rw [h] <;> decide
  clear hStart
  suffices decisionScope u.pc = true ∧ Holds u.regs (openingDenominatorRegisters p l g) from this.2
  induction hLocal with
  | refl => exact ⟨hs,hFrame⟩
  | tail hPath hStep ih =>
    obtain ⟨hPc,hKeep⟩ := decisionStep ih.1 hStep
    obtain ⟨hWarp,hBase,hStats,hBits,hNeg,_⟩ := ih.2
    exact ⟨hPc,(hKeep 1062 (by decide)).trans hWarp,(hKeep 2535 (by decide)).trans hBase,
      (hKeep 5127 (by decide)).trans hStats,(hKeep 7132 (by decide)).trans hBits,
      (hKeep 1230 (by decide)).trans hNeg,trivial⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
