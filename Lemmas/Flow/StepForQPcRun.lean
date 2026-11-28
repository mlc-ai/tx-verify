-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQPcR

@[expose] public section

/-! # The strict chain with the run's own states and the invariant at the window's start pinned

`strictQPR_windowPc` asks the invariant at the window's first state for every run position.
Here it is asked at the position the window starts at (`Pr t (es.drop k0)`), and the conclusion
gives the run's own state before the event, so a later window can take its invariant from it. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **The strict chain with `P` after each event**, with the run's states. -/
theorem strictQP_fromPcRun (hC : C.SoundU) {Q P : TState → Prop} {Wf : Event → Prop}
    {Ok : C.D → Prop} {Pr : TState → List Event → Prop}
    (hS : ∀ d e, Ok d → C.StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = C.pc d → C.next d e = some (some d') → Ok d')
    (hP : PosStep (K := K) (A := A) (L := L) (g := g) Pr P)
    {t : TState} {es : List Event} {o : Option TState} (hr : Run K A L g t es o) :
    Pr t es → ∀ {n : Nat} {d dn : C.D} {e' : Event}, Ok d →
      (∃ t1, Relation.ReflTransGen (Tau K A L g) t t1 ∧ C.Good (some d) t1 ∧ Q t1) →
      (∀ e ∈ es.take n, Wf e) → C.toMachine.after (some d) (es.take n) = some (some dn) →
      es[n]? = some e' →
      Ok dn ∧ ∃ t0 t1 o', Run K A L g t (es.take n) (some t0) ∧
        Relation.ReflTransGen (Tau K A L g) t0 t1 ∧ C.Good (some dn) t1 ∧ Q t1 ∧
        EStep K A L g t1 e' o' := by
  induction hr with
  | nil t => intro _ n d dn e' _ _ _ _ h; simp at h
  | @step t t1 t2 e0 rest o hl he hrest ih =>
    intro hPrt n d dn e' hOkd hland hW hafter hn
    obtain ⟨hPr2, hP2⟩ := hP hPrt hl he
    obtain ⟨s1, hl1, hg1, hq1⟩ := hland
    obtain rfl := stop_unique hl hl1 (stops_of_estep he) (stops_of_good hC hg1)
    cases n with
    | zero =>
      rw [List.take_zero] at hafter
      change some (some d) = some (some dn) at hafter
      obtain rfl := Option.some.inj (Option.some.inj hafter)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      exact ⟨hOkd, t, _, _, Run.nil t, hl, hg1, hq1, he⟩
    | succ n =>
      simp only [List.take_succ_cons, List.mem_cons, forall_eq_or_imp] at hW hafter
      simp only [List.getElem?_cons_succ] at hn
      obtain ⟨hW0, hW⟩ := hW
      obtain ⟨ins, hc, hf⟩ := fired_of_good hC hg1 he
      rcases hS d e0 hOkd ins hg1.1 hg1.2 hc hq1 hW0 hf hP2 with
        ⟨d1, t', hn1, hl', hg', hq'⟩ | ⟨hn1, -⟩
      · have hafter' : C.toMachine.after (some d1) (rest.take n) = some (some dn) := by
          change (C.next d e0).bind _ = _ at hafter
          rw [hn1] at hafter
          exact hafter
        obtain ⟨hok, t0, t1', o', hrun, hs, hg2, hq2, hes⟩ :=
          ih hPr2 (hOk d e0 d1 hOkd hW0 (fires_pc hf) hn1) ⟨t', hl', hg', hq'⟩ hW hafter' hn
        exact ⟨hok, t0, t1', o', by rw [List.take_succ_cons]; exact Run.step hl he hrun, hs,
          hg2, hq2, hes⟩
      · change (C.next d e0).bind _ = _ at hafter
        rw [hn1] at hafter
        cases hafter
  | @last t t1 e hl he =>
    intro hPrt n d dn e' hOkd hland hW hafter hn
    obtain ⟨s1, hl1, hg1, hq1⟩ := hland
    obtain rfl := stop_unique hl hl1 (stops_of_estep he) (stops_of_good hC hg1)
    cases n with
    | zero =>
      rw [List.take_zero] at hafter
      change some (some d) = some (some dn) at hafter
      obtain rfl := Option.some.inj (Option.some.inj hafter)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      exact ⟨hOkd, t, _, _, Run.nil t, hl, hg1, hq1, he⟩
    | succ n => simp at hn

/-- **The strict chain after a UB-tolerant prefix**, the invariant at `dk0` taken from the run
position `k0`, with the run's states. -/
theorem strictQPRun_windowPc (hC : C.SoundU) {Q P : TState → Prop} {Wf : Event → Prop}
    {Ok : C.D → Prop} {Pr : TState → List Event → Prop}
    (hS : ∀ d e, Ok d → C.StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = C.pc d → C.next d e = some (some d') → Ok d')
    (hP : PosStep (K := K) (A := A) (L := L) (g := g) Pr P)
    {u : TState} {es : List Event} {o : Option TState} (hr : Run K A L g u es o) :
    Pr u es → ∀ {k0 m : Nat} {d dk0 dn : C.D} {e' : Event}, C.toMachineU.Reach (some d) u →
      C.toMachine.after (some d) (es.take k0) = some (some dk0) → Ok dk0 →
      (∀ t t1, Pr t (es.drop k0) → Relation.ReflTransGen (Tau K A L g) t t1 →
        C.Good (some dk0) t1 → Q t1) → (∀ e ∈ (es.drop k0).take (m + 1), Wf e) →
      C.toMachine.after (some dk0) ((es.drop k0).take (m + 1)) = some (some dn) →
      es[k0 + (m + 1)]? = some e' →
      Ok dn ∧ ∃ t0 t1 o', Run K A L g u (es.take (k0 + (m + 1))) (some t0) ∧
        Relation.ReflTransGen (Tau K A L g) t0 t1 ∧ C.Good (some dn) t1 ∧ Q t1 ∧
        EStep K A L g t1 e' o' := by
  induction hr with
  | nil t => intro _ k0 m d dk0 dn e' _ _ _ _ _ _ h; simp at h
  | @step t t1 t2 e0 rest o hl he hrest ih =>
    intro hPrt k0 m d dk0 dn e' hreach hafter hOkd hQ0 hW hafter2 hn
    have hg := hreach t1 hl (stops_of_estep he)
    have hgood : C.Good (some d) t1 := good_of_goodU_fires hg he
    cases k0 with
    | zero =>
      rw [List.take_zero] at hafter
      change some (some d) = some (some dk0) at hafter
      obtain rfl := Option.some.inj (Option.some.inj hafter)
      simp only [List.drop_zero, Nat.zero_add] at hW hafter2 hn hQ0 ⊢
      exact strictQP_fromPcRun hC hS hOk hP (Run.step hl he hrest) hPrt hOkd
        ⟨t1, hl, hgood, hQ0 t t1 hPrt hl hgood⟩ hW hafter2 hn
    | succ k =>
      simp only [List.take_succ_cons] at hafter
      change (C.next d e0).bind _ = _ at hafter
      rcases hq : C.next d e0 with _ | _ | d1
      · rw [hq] at hafter; cases hafter
      · rw [hq] at hafter
        change C.toMachine.after none _ = _ at hafter
        rw [after_none_eq] at hafter
        cases hafter
      · rw [hq] at hafter
        change C.toMachine.after (some d1) _ = _ at hafter
        obtain ⟨mm, hm, hf⟩ := he
        have hout := hC.machine.out_eq hg
        have hf' : Fires t1.pc (C.toMachineU.tmpl (some d) t1) e0 (some t2) := by
          have : C.toMachineU.tmpl (some d) t1 = mm := by
            simp only [toMachineU, tmpl, hm]
          rw [this]; exact hf
        rcases hC.machine.step hg hf' with ⟨σ', hn', hreach'⟩ | ⟨hn', -⟩
        · have hn'' : C.next d e0 = some σ' := hn'
          rw [hq] at hn''
          obtain rfl := Option.some.inj hn''
          simp only [List.drop_succ_cons] at hW hafter2 hQ0
          rw [Nat.succ_add] at hn
          simp only [List.getElem?_cons_succ] at hn
          obtain ⟨hok, t0, t1', o', hrun, hs, hg2, hq2, hes⟩ :=
            ih (hP hPrt hl ⟨mm, hm, hf⟩).1 hreach' hafter hOkd hQ0 hW hafter2 hn
          refine ⟨hok, t0, t1', o', ?_, hs, hg2, hq2, hes⟩
          rw [Nat.succ_add, List.take_succ_cons]
          exact Run.step hl ⟨mm, hm, hf⟩ hrun
        · have hn'' : C.next d e0 = none := hn'
          rw [hq] at hn''; cases hn''
  | @last t t1 e hl he =>
    intro _ k0 m d dk0 dn e' hreach hafter hOkd hQ0 hW hafter2 hn
    cases k0 with
    | zero => simp at hn
    | succ k => rw [Nat.succ_add] at hn; simp at hn

end

end PTX.Flow.Code
