-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQPc

@[expose] public section

/-! # The strict chain, with a fact about the states the run reaches after each event

`Code.StepForQP` is `StepForQ` (`Lemmas/Flow/StepForQ.lean`) for a step that may use `P u` of the
state `u` right after its event. A step that needs a fact about the values the lane computes next
(the ideal rule of an `add` without a rounding modifier does not decline) cannot prove it from
`Q` alone: the fact is about the states of the lane's own run. `strictQP_fromPc` and
`strictQP_windowPc` are the chains of `Lemmas/Flow/StepForQPc.lean` over a position invariant
`Pr t es` ("`t` is a state of the run whose remaining events are `es`"), which the caller shows
for the run's own states and which gives `P` after each event (`hPr`). -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The strict step obligation of one state for one event, with `P` of the state after the event. -/
def StepForQP (C : Code K A L g) (Q P : TState → Prop) (Wf : Event → Prop) (d : C.D)
    (e : Event) : Prop :=
  ∀ {t u : TState} (ins : Instr), C.AtD d t → C.inv d → K.code[C.pc d]? = some ins → Q t →
    Wf e → Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) → P u →
    (∃ d' t', C.next d e = some (some d') ∧ Relation.ReflTransGen (Tau K A L g) u t' ∧
        C.Good (some d') t' ∧ Q t') ∨
      (C.next d e = none ∧ Machine.Dead (K := K) (A := A) (L := L) (g := g) u)

theorem StepForQ.toP {Q : TState → Prop} (P : TState → Prop) {Wf : Event → Prop} {d : C.D}
    {e : Event} (h : C.StepForQ Q Wf d e) : C.StepForQP Q P Wf d e :=
  fun ins ha hi hc hq hw hf _ => h ins ha hi hc hq hw hf

/-- The position invariant is kept by an event of the run and gives `P` after it. -/
def PosStep (Pr : TState → List Event → Prop) (P : TState → Prop) : Prop :=
  ∀ {t t1 t2 : TState} {e0 : Event} {rest : List Event}, Pr t (e0 :: rest) →
    Relation.ReflTransGen (Tau K A L g) t t1 → EStep K A L g t1 e0 (some t2) →
    Pr t2 rest ∧ P t2

/-- **The strict chain** with `P` after each event. -/
theorem strictQP_fromPc (hC : C.SoundU) {Q P : TState → Prop} {Wf : Event → Prop}
    {Ok : C.D → Prop} {Pr : TState → List Event → Prop}
    (hS : ∀ d e, Ok d → C.StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = C.pc d → C.next d e = some (some d') → Ok d')
    (hP : PosStep (K := K) (A := A) (L := L) (g := g) Pr P)
    {t : TState} {es : List Event} {o : Option TState} (hr : Run K A L g t es o) :
    Pr t es → ∀ {n : Nat} {d dn : C.D} {e' : Event}, Ok d →
      (∃ t1, Relation.ReflTransGen (Tau K A L g) t t1 ∧ C.Good (some d) t1 ∧ Q t1) →
      (∀ e ∈ es.take n, Wf e) → C.toMachine.after (some d) (es.take n) = some (some dn) →
      es[n]? = some e' →
      Ok dn ∧ ∃ t1 o', C.Good (some dn) t1 ∧ Q t1 ∧ EStep K A L g t1 e' o' := by
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
      exact ⟨hOkd, _, _, hg1, hq1, he⟩
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
        exact ih hPr2 (hOk d e0 d1 hOkd hW0 (fires_pc hf) hn1) ⟨t', hl', hg', hq'⟩ hW hafter' hn
      · change (C.next d e0).bind _ = _ at hafter
        rw [hn1] at hafter
        cases hafter
  | @last t t1 e hl he =>
    intro _ n d dn e' hOkd hland hW hafter hn
    obtain ⟨s1, hl1, hg1, hq1⟩ := hland
    obtain rfl := stop_unique hl hl1 (stops_of_estep he) (stops_of_good hC hg1)
    cases n with
    | zero =>
      rw [List.take_zero] at hafter
      change some (some d) = some (some dn) at hafter
      obtain rfl := Option.some.inj (Option.some.inj hafter)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      exact ⟨hOkd, _, _, hg1, hq1, he⟩
    | succ n => simp at hn

/-- **The strict chain after a UB-tolerant prefix**, with `P` after each event. -/
theorem strictQP_windowPc (hC : C.SoundU) {Q P : TState → Prop} {Wf : Event → Prop}
    {Ok : C.D → Prop} {Pr : TState → List Event → Prop}
    (hS : ∀ d e, Ok d → C.StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = C.pc d → C.next d e = some (some d') → Ok d')
    (hP : PosStep (K := K) (A := A) (L := L) (g := g) Pr P)
    {u : TState} {es : List Event} {o : Option TState} (hr : Run K A L g u es o) :
    Pr u es → ∀ {k0 m : Nat} {d dk0 dn : C.D} {e' : Event}, C.toMachineU.Reach (some d) u →
      C.toMachine.after (some d) (es.take k0) = some (some dk0) → Ok dk0 →
      (∀ t, C.Good (some dk0) t → Q t) → (∀ e ∈ (es.drop k0).take (m + 1), Wf e) →
      C.toMachine.after (some dk0) ((es.drop k0).take (m + 1)) = some (some dn) →
      es[k0 + (m + 1)]? = some e' →
      Ok dn ∧ ∃ t1 o', C.Good (some dn) t1 ∧ Q t1 ∧ EStep K A L g t1 e' o' := by
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
      simp only [List.drop_zero, Nat.zero_add] at hW hafter2 hn
      exact strictQP_fromPc hC hS hOk hP (Run.step hl he hrest) hPrt hOkd
        ⟨t1, hl, hgood, hQ0 t1 hgood⟩ hW hafter2 hn
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
          simp only [List.drop_succ_cons] at hW hafter2
          rw [Nat.succ_add] at hn
          simp only [List.getElem?_cons_succ] at hn
          exact ih (hP hPrt hl ⟨mm, hm, hf⟩).1 hreach' hafter hOkd hQ0 hW hafter2 hn
        · have hn'' : C.next d e0 = none := hn'
          rw [hq] at hn''; cases hn''
  | @last t t1 e hl he =>
    intro _ k0 m d dk0 dn e' hreach hafter hOkd hQ0 hW hafter2 hn
    cases k0 with
    | zero => simp at hn
    | succ k => rw [Nat.succ_add] at hn; simp at hn

end

end PTX.Flow.Code
