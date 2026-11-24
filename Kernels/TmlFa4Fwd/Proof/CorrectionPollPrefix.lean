-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLinearPrefix
public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma

noncomputable section

def correctionPoll : Fin 5 → Nat × Nat
  | 0 => (8473, 9888)
  | 1 => (8476, 9889)
  | 2 => (8769, 9890)
  | 3 => (8772, 9891)
  | 4 => (9201, 9892)

private theorem correctionPollCode (i : Fin 5) :
    let pc := (correctionPoll i).1
    let d := (correctionPoll i).2
    (∃ base phase, kernel.code[pc]? = some
      ⟨none, .mbarWait d base 0 (.reg phase) true .cta⟩) ∧
    kernel.code[pc + 1]? = some ⟨some (d, false), .bra (pc + 3) true⟩ ∧
    kernel.code[pc + 2]? = some ⟨none, .bra pc true⟩ := by
  fin_cases i
  · exact ⟨⟨_, _, Flow.code_8473⟩, Flow.code_8474, Flow.code_8475⟩
  · exact ⟨⟨_, _, Flow.code_8476⟩, Flow.code_8477, Flow.code_8478⟩
  · exact ⟨⟨_, _, Flow.code_8769⟩, Flow.code_8770, Flow.code_8771⟩
  · exact ⟨⟨_, _, Flow.code_8772⟩, Flow.code_8773, Flow.code_8774⟩
  · exact ⟨⟨_, _, Flow.code_9201⟩, Flow.code_9202, Flow.code_9203⟩

theorem correctionWait_step (i : Fin 5) {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (hp : s.pc = (correctionPoll i).1)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ ok : Bool, u = next (setReg s (correctionPoll i).2 (.pred ok)) ∧
      e.counts = ok ∧ s.fault = none ∧
      ∃ loc parity scope, e = ⟨s.pc, .wait loc parity ok true scope⟩ := by
  obtain ⟨ins, hc, _, hr⟩ := estep_event_source he
  obtain ⟨⟨base, phase, h⟩, _, _⟩ := correctionPollCode i
  rw [hp, h] at hc
  obtain rfl := Option.some.inj hc
  obtain ⟨loc, parity, ok, scope, hKind, rfl⟩ := fires_wait hr
  have hf : s.fault = none := by
    cases hF : s.fault
    · rfl
    · obtain ⟨m, hm, hFire⟩ := he
      simp only [out, hF, Out.ev.injEq] at hm
      subst m
      cases hFire.2
  refine ⟨ok, rfl, ?_, hf, loc, parity, scope, hKind⟩
  rw [hKind]
  cases ok <;> rfl

theorem correctionPollLocals (i : Fin 5) {l : Launch} {g : Nat} {s : TState}
    (hp : s.pc = (correctionPoll i).1) (hf : s.fault = none) (ok : Bool) :
    let v := next (setReg s (correctionPoll i).2 (.pred ok))
    ∃ u, run kernel Assumptions.all l g (if ok then 1 else 2) v = some u ∧
      u.pc = (if ok then (correctionPoll i).1 + 3 else (correctionPoll i).1) ∧
      u.sub ≤ s.sub ∧ u.fault = none ∧ u.regs = v.regs ∧
      (s.sub = 0 → u.sub = 0) ∧ (s.acc = [] → u.acc = []) := by
  dsimp only
  let v := next (setReg s (correctionPoll i).2 (.pred ok))
  let pc := (correctionPoll i).1
  let d := (correctionPoll i).2
  obtain ⟨_, hBranch, hRetry⟩ := correctionPollCode i
  change kernel.code[pc + 1]? = some ⟨some (d, false), .bra (pc + 3) true⟩ at hBranch
  change kernel.code[pc + 2]? = some ⟨none, .bra pc true⟩ at hRetry
  have hv : v.pc = pc + 1 := by simp [v, next, setReg, hp, pc]
  have hvF : v.fault = none := hf
  have hS : tauStep kernel Assumptions.all l g v =
      some (if ok then {v with pc := pc + 3} else skip v) := by
    rw [Assumptions.tauStep_all_eq_nil
      (by rw [hv]; fin_cases i <;> decide) (hv.symm ▸ hBranch) rfl]
    have hRead : readReg v d = .ok (.pred ok) := by
      simp [v, d, readReg, next, setReg, pure, Except.pure]
    unfold tauStep out
    rw [hvF, hv, hBranch]
    have hGuard : guardHolds v (some (d, false)) = .ok ok := by
      cases ok <;> simp [guardHolds, hRead, bind, Except.bind, pure, Except.pure]
    have hLocal : (Op.bra (pc + 3) true).isLocal = true := rfl
    have hRule : (Op.bra (pc + 3) true).rule = some .threadBranch := rfl
    cases ok
    · simp [hGuard]
    · simpa [hGuard, hLocal, hRule, execLocalA_nil, execLocal, execBranch, pure, Except.pure]
        using hvF
  cases ok
  · let w := skip v
    have hw : w.pc = pc + 2 := by simp [w, skip, hv]
    have hwF : w.fault = none := hf
    have hBack : tauStep kernel Assumptions.all l g w = some {w with pc := pc} := by
      rw [Assumptions.tauStep_all_eq_nil
        (by rw [hw]; fin_cases i <;> decide) (hw.symm ▸ hRetry) rfl]
      unfold tauStep out
      rw [hwF, hw, hRetry]
      have hLocal : (Op.bra pc true).isLocal = true := rfl
      have hRule : (Op.bra pc true).rule = some .threadBranch := rfl
      simpa [hLocal, hRule, guardHolds, execLocalA_nil, execLocal, execBranch, pure, Except.pure]
        using hwF
    refine ⟨{w with pc := pc}, ?_, rfl, Nat.zero_le _, hf, rfl, fun _ => rfl, fun _ => rfl⟩
    change run kernel Assumptions.all l g 2 v = _
    simp only [run, hS, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
    change (tauStep kernel Assumptions.all l g w).bind (fun x => some x) = _
    rw [hBack]
    rfl
  · refine ⟨{v with pc := pc + 3}, ?_, rfl, le_rfl, hf, rfl, id, id⟩
    change run kernel Assumptions.all l g 1 v = _
    simp only [run, hS, ↓reduceIte, Option.bind_some]

/-- A finite prefix through a correction spin contributes at most its leaving acquire.
A terminal fault contributes one when the prefix ends before leaving the spin. -/
theorem cutCorrectionPoll (i : Fin 5) {l : Launch} {g cutoff : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hp : s.pc = (correctionPoll i).1) (hIn : s.pc < cutoff)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil cutoff visits ≤ 1 ∨
    ∃ u tail supers, u.pc = (correctionPoll i).1 + 3 ∧ u.fault = none ∧ u.sub ≤ s.sub ∧
      Walk kernel Assumptions.all l g u tail supers ∧
      countedUntil cutoff visits ≤ 1 + countedUntil cutoff supers := by
  generalize hfuel : visits.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s events visits with
  | h fuel ih =>
    cases hw with
    | stop => exact .inl (by simp [countedUntil])
    | tau ht _ =>
      obtain ⟨base, phase, hc⟩ := (correctionPollCode i).1
      rw [← hp] at hc
      unfold Tau out at ht
      cases hF : s.fault <;> simp [hF, hc, guardHolds, Op.isLocal, pure, Except.pure] at ht
    | last he => exact .inl (by
        simp only [countedUntil, List.takeWhile_cons, visit_pc, hIn, decide_true, ↓reduceIte,
          List.filterMap_cons, visit_ev]
        exact List.countP_le_length (p := Event.counts) (l := [ _ ]))
    | @ev s v e events visits he hWalk =>
      obtain ⟨ok, rfl, hCount, hf, _⟩ := correctionWait_step i hp he
      obtain ⟨u, hRun, hu, hSub, hFault, _⟩ := correctionPollLocals (l := l) (g := g) i hp hf ok
      have hPrefix : countedUntil cutoff
          (visit kernel l g s (some e) :: visits) =
            countedUntil cutoff visits + if ok then 1 else 0 := by
        simp [countedUntil, visit_pc, visit_ev, hIn, List.countP_cons, hCount]
      rw [hPrefix]
      rcases advanceWalkLocals hRun hWalk with he | ⟨post, hLength, hLater, hW⟩
      · subst events
        exact .inl (by simp [zeroCountNoEvents hWalk]; split <;> omega)
      · have hTail := hLater cutoff
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hu hRun hPrefix ⊢
          have hLt : post.length < fuel := by
            simp only [List.length_cons] at hfuel
            omega
          rcases ih post.length hLt hu (hu.symm ▸ hp ▸ hIn) hW rfl with h |
              ⟨w, es, vs, hPc, hF, hS, hW, hB⟩
          · exact .inl (hTail.trans h)
          · exact .inr ⟨w, es, vs, hPc, hF, hS.trans hSub, hW, hTail.trans hB⟩
        · simp only [↓reduceIte] at hu ⊢
          exact .inr ⟨u, events, post, hu, hFault, hSub, hW, by omega⟩

/-- A continuing walk crosses a correction poll only through its successful acquire.
The suffix retains the input registers other than the poll's predicate. -/
theorem correctionPollTrace (i : Fin 5) {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} (ht : At s (correctionPoll i).1 F)
    (hFresh : ∀ rv ∈ F, rv.1 ≠ (correctionPoll i).2)
    {events : List Event} {visits : List Visit} {target : Event}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hTarget : target ∈ events) (hLate : (correctionPoll i).1 < target.pc) :
    ∃ (before : List Event) (loc : Loc) (parity : Nat) (scope : MbarScope)
      (u : TState) (after : List Event) (post : List Visit),
      events = before ++ ⟨(correctionPoll i).1, .wait loc parity true true scope⟩ :: after ∧
      At u ((correctionPoll i).1 + 3) F ∧
      Walk kernel Assumptions.all l g u after post ∧ target ∈ after ∧
      ∃ source returned, At source (correctionPoll i).1 F ∧
        EStep kernel Assumptions.all l g source
          ⟨(correctionPoll i).1, .wait loc parity true true scope⟩ (some returned) := by
  generalize hLen : visits.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s events visits with
  | h fuel ih =>
    cases hw with
    | stop => simp at hTarget
    | tau he _ =>
      obtain ⟨base, phase, hc⟩ := (correctionPollCode i).1
      rw [← ht.1] at hc
      simp [Tau, out, ht.2.2.2.1, hc, guardHolds, Op.isLocal, pure, Except.pure] at he
    | last he =>
      obtain rfl := List.mem_singleton.mp hTarget
      exact (Nat.ne_of_lt hLate ((estep_source_pc he).trans ht.1).symm).elim
    | @ev s v e events visits he hw =>
      obtain ⟨ok, rfl, _, hf, loc, parity, scope, rfl⟩ := correctionWait_step i ht.1 he
      obtain ⟨u, hRun, hu, _, hF, hRegs, hSub, hAcc⟩ :=
        correctionPollLocals (l := l) (g := g) i ht.1 hf ok
      have hAt : At u (if ok then (correctionPoll i).1 + 3 else (correctionPoll i).1) F := by
        refine ⟨hu, hSub ht.2.1, hAcc ht.2.2.1, hF, ?_⟩
        rw [hRegs]
        exact (ht.set (r := (correctionPoll i).2) (v := .pred ok) hFresh).2.2.2.2.2
      have hMem : target ∈ events := by
        rcases List.mem_cons.mp hTarget with he' | h
        · have hp := congrArg Event.pc he'
          dsimp only at hp
          rw [ht.1] at hp
          omega
        · exact h
      rcases advanceWalkLocals hRun hw with h | ⟨post, hLength, _, hWalk⟩
      · subst events
        simp at hMem
      cases ok with
      | false =>
        have hLt : post.length < fuel := by simp at hLen; omega
        obtain ⟨before, loc', parity', scope', v', after, trail, hes, hv, hW, hM, hEvent⟩ :=
          ih post.length hLt hAt hWalk hMem rfl
        exact ⟨_ :: before, loc', parity', scope', v', after, trail,
          by rw [List.cons_append, hes], hv, hW, hM, hEvent⟩
      | true =>
        exact ⟨[], loc, parity, scope, u, events, post,
          by rw [ht.1]; rfl, hAt, hWalk, hMem, s, _, ht, by simpa only [ht.1] using he⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
