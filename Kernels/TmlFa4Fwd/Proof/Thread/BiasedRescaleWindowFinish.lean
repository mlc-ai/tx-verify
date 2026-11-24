-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleBiasedScoreInputs
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

set_option maxRecDepth 100000 in
private theorem quietBiasArithmetic {pc : Nat} {ins : Instr} (hLo : 5279 ≤ pc)
    (hHi : pc < 5682) (hc : kernel.code[pc]? = some ins) :
    ins.op.isLocal = true ∧ Epilogue.schedulerFallsThrough ins.op = true := by
  have hAudit : ((kernel.code.drop 5279).take (5682-5279)).all
      (fun ins => ins.op.isLocal && Epilogue.schedulerFallsThrough ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hMem : ins ∈ (kernel.code.drop 5279).take (5682-5279) := by
    apply List.mem_of_getElem? (i := pc-5279)
    rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
  simpa only [Bool.and_eq_true] using List.all_eq_true.mp hAudit ins hMem

private theorem biasArithmeticLocalStep {l : Launch} {g : Nat} {s u : TState}
    (hs : 5279 ≤ s.pc ∧ s.pc ≤ 5682) (hTau : Tau kernel Assumptions.all l g s u) :
    5279 ≤ u.pc ∧ u.pc ≤ 5682 := by
  obtain ⟨ins,hCode,_,hExec⟩ := tauScoreSource hTau
  have hHi : s.pc < 5682 := by
    rcases Nat.eq_or_lt_of_le hs.2 with hAt | hLess
    · rw [hAt,Flow.code_5682] at hCode
      obtain rfl := Option.some.inj hCode
      rcases hExec with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
      · cases hGuard
      · cases hLocal
    · exact hLess
  rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hRun⟩
  · change 5279 ≤ s.pc+1 ∧ s.pc+1 ≤ 5682
    omega
  · rcases scoreExecLocal hRun with hFrame | ⟨seg,hSite,hMatch,hSem⟩
    · have hQuiet := (quietBiasArithmetic hs.1 hHi hCode).2
      have hPc := hFrame.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra => simp [Epilogue.schedulerFallsThrough,hOp] at hQuiet
      case brx => simp [Epilogue.schedulerFallsThrough,hOp] at hQuiet
      all_goals omega
    · have hAudit : Assumptions.swExp2Sites.all
          (fun site => decide (site < 5279 ∨ 5682 < site)) = true := by decide
      have hOut := of_decide_eq_true (List.all_eq_true.mp hAudit s.pc hSite)
      omega

private theorem biasArithmeticFirstReturn {l : Launch} {g : Nat} {s t u : TState} {e : Event}
    (hs : s.pc = 5279) (hPath : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (he : EStep kernel Assumptions.all l g t e (some u)) : e.pc = 5682 := by
  have hBound : 5279 ≤ t.pc ∧ t.pc ≤ 5682 := by
    clear he
    induction hPath with
    | refl => exact ⟨hs.ge,by omega⟩
    | tail _ hStep ih => exact biasArithmeticLocalStep ih hStep
  have hAt : t.pc = 5682 := by
    rcases Nat.eq_or_lt_of_le hBound.2 with hAt | hLt
    · exact hAt
    obtain ⟨i,hCode,hNonlocal,_⟩ := estep_event_source he
    have hLocal := (quietBiasArithmetic hBound.1 hLt hCode).1
    exact (Bool.false_ne_true (hNonlocal.symm.trans hLocal)).elim
  exact (estep_source_pc he).trans hAt

/-- The affine Bias cursor and the recorded rescale word have the same trace index.
Only local arithmetic can appear between them on the selected visit. -/
theorem biasedAffineEntryIndex {l : Launch} {X : Execution} {g start enter pos : Nat}
    {s : TState} {ending : Option TState} {a : Acc} {bytes : List Byte}
    (hs : At s (biasBodyStart true) [])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop enter) ending)
    (hStart : start ≤ enter) (hEnter : enter ≤ pos)
    (hNoWrite : ∀ k, start ≤ k → k < pos → ∀ e, X.get (g,k) = some e → e.pc ≠ 5682)
    (he : StatisticsStore X (g,pos) (rescaleStore true) a bytes) :
    enter = pos := by
  by_contra hNe
  have hLt : enter < pos := lt_of_le_of_ne hEnter hNe
  have hExtent : pos < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hLength : 1 < ((X.tr g).drop enter).length := by
    rw [List.length_drop]
    omega
  have hIndex (front : Event) (suffix : List Event)
      (hCons : (X.tr g).drop enter = front::suffix) :
      X.get (g,enter) = some front := by
    change (X.tr g)[enter]? = some front
    rw [← Nat.add_zero enter,← List.getElem?_drop,hCons]
    rfl
  generalize hEq : (X.tr g).drop enter = events at hr hLength
  cases hr with
  | nil => simp at hLength
  | last => simp at hLength
  | step hp he _ =>
    have hPc := biasArithmeticFirstReturn hs.1 hp he
    exact (hNoWrite enter hStart hLt _ (hIndex _ _ hEq)) hPc

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
