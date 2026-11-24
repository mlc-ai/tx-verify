-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopLocal
public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Softmax

noncomputable section

/-- Correction also uses the explicit load wait of the final x8 copies. -/
def correctionReturningOp (op : Op) : Bool :=
  scoreEventOp op || match op with | .tcWaitLd => true | _ => false

theorem correctionEventProgress {l : Launch} {g r : Nat} {s u : TState}
    {e : Event} {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
    (hOp : correctionReturningOp ins.op = true) (hSub : s.sub ≤ 3)
    (hKeep : r ∉ scoreEventWrites ins.op)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ScoreEventProgress s u ∧ u.regs r = s.regs r := by
  simp only [correctionReturningOp, Bool.or_eq_true] at hOp
  rcases hOp with h | h
  · exact scoreEventStep hc h hSub hKeep he
  · have hOp : ins.op = .tcWaitLd := by cases hh : ins.op <;> simp_all
    obtain ⟨a, ha, _, hFire⟩ := estep_event_source he
    rw [hc] at ha
    obtain rfl := Option.some.inj ha
    rw [hOp] at hFire
    simp only [eventTmpl, tcTmpl] at hFire
    have hNext : u = next s := by
      split at hFire
      · exact Option.some.inj hFire.2
      · simp [ofExec, Fires, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hFire
    subst u
    exact ⟨⟨hSub, .inl ⟨rfl, rfl⟩⟩, rfl⟩

/-- Outside the software exponent sites, every actual correction local step either skips
its guarded instruction or preserves that instruction's decoded local frame. -/
theorem correctionTauFrame {l : Launch} {g : Nat} {s u : TState}
    (hPc : s.pc ∉ Assumptions.swExp2Sites) (ht : Tau kernel Assumptions.all l g s u) :
    ∃ i, kernel.code[s.pc]? = some i ∧ s.fault = none ∧
      (u = skip s ∧ guardHolds s i.guard = .ok false ∨
        guardHolds s i.guard = .ok true ∧ i.op.isLocal = true ∧ LocalFrame i.op s u) := by
  unfold Tau out at ht
  cases hf : s.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : kernel.code[s.pc]? with
    | none => simp only [hc, reduceCtorEq] at ht
    | some i =>
      simp only [hc] at ht
      refine ⟨i, rfl, rfl, ?_⟩
      cases hG : guardHolds s i.guard with
      | error f => simp only [hG, reduceCtorEq] at ht
      | ok guard =>
        cases guard
        · simp only [hG, Out.tau.injEq] at ht
          exact .inl ⟨ht.symm, rfl⟩
        · simp only [hG] at ht
          by_cases hLoc : i.op.isLocal = true
          · simp only [hLoc, ite_true] at ht
            cases hExec : execLocalA Assumptions.all l g s i.op with
            | error f => simp only [hExec, reduceCtorEq] at ht
            | ok v =>
              simp only [hExec, Out.tau.injEq] at ht
              subst v
              exact .inr ⟨rfl, hLoc, (scoreExecLocal hExec).resolve_right
                (fun ⟨_, hSite, _, _⟩ => hPc hSite)⟩
          · simp only [hLoc, ite_false, reduceCtorEq] at ht

end
end PTX.Kernels.TmlFa4Fwd.Correction
