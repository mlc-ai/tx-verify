-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StrictLift

@[expose] public section

/-! # A strict step under an invariant, and the strict chain

`Code.StepForQ Q Wf d e` (`StepFor` of `Lemmas/Flow/StrictWindow.lean`, with an invariant `Q` of the
concrete state and a well-formedness condition `Wf` of the event): from a state of `d` satisfying
`Q`, the event `e` (with `Wf e`) is followed by local steps to a strictly good state of the
successor, which satisfies `Q` again. There is no fault alternative, and no `some none` successor.

* `strictQ_from`: the chain. From a strictly good state satisfying `Q`, along a run whose events
  satisfy `Wf`, the state before every event is strictly good and satisfies `Q`, if the steps of the
  machine's states that the run reaches (`Ok`, closed under `next`) obey `StepForQ`.
* `strictQ_window`: the same after a UB-tolerant prefix: the machine follows the run tolerantly to
  the state `dk0` before the event `k0` (a state that fires a continuing event is strictly good,
  `good_of_goodU_fires`), where `Q` holds by the state alone, and the chain starts there.
* `StepFor.toQ`: a strict step whose landing states satisfy `Q` by themselves is a `StepForQ`.
* `counted_stepForQ`, `glue_inl_stepForQ`, `glue_inr_stepForQ`, `loopGlue_inl_stepForQ`,
  `loopGlue_inr_stepForQ`: the lifts of `Lemmas/Flow/StrictLift.lean`. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The strict step obligation of one state for one event, under the invariant `Q` of the concrete
state and the well-formedness `Wf` of the event. -/
def StepForQ (C : Code K A L g) (Q : TState → Prop) (Wf : Event → Prop) (d : C.D) (e : Event) :
    Prop :=
  ∀ {t u : TState} (ins : Instr), C.AtD d t → C.inv d → K.code[C.pc d]? = some ins → Q t →
    Wf e → Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) →
    (∃ d' t', C.next d e = some (some d') ∧ Relation.ReflTransGen (Tau K A L g) u t' ∧
        C.Good (some d') t' ∧ Q t') ∨
      (C.next d e = none ∧ Machine.Dead (K := K) (A := A) (L := L) (g := g) u)

/-- A strict step whose landing states satisfy the invariant by themselves. -/
theorem StepFor.toQ {Q : TState → Prop} {Wf : Event → Prop} {d : C.D} {e : Event}
    (h : C.StepFor d e) (hn : C.next d e ≠ some none)
    (hq : ∀ d' t', C.next d e = some (some d') → C.Good (some d') t' → Q t') :
    C.StepForQ Q Wf d e := by
  intro t u ins hat hinv hc _ _ hf
  rcases h ins hat hinv hc hf with (h1 | ⟨d', t', h1, h2, h3⟩) | h4
  · exact absurd h1 hn
  · exact .inl ⟨d', t', h1, h2, h3, hq d' t' h1 h3⟩
  · exact .inr h4

/-- **The strict chain**: from a strictly good state satisfying `Q` (after local steps from `t`),
the state before every event `n` of the run is strictly good and satisfies `Q`. -/
theorem strictQ_from (hC : C.SoundU) {Q : TState → Prop} {Wf : Event → Prop} {Ok : C.D → Prop}
    (hS : ∀ d e, Ok d → C.StepForQ Q Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → C.next d e = some (some d') → Ok d')
    {t : TState} {es : List Event} {o : Option TState} (hr : Run K A L g t es o) :
    ∀ {n : Nat} {d dn : C.D} {e' : Event}, Ok d →
      (∃ t1, Relation.ReflTransGen (Tau K A L g) t t1 ∧ C.Good (some d) t1 ∧ Q t1) →
      (∀ e ∈ es.take n, Wf e) → C.toMachine.after (some d) (es.take n) = some (some dn) →
      es[n]? = some e' →
      Ok dn ∧ ∃ t1 o', C.Good (some dn) t1 ∧ Q t1 ∧ EStep K A L g t1 e' o' := by
  induction hr with
  | nil t => intro n d dn e' _ _ _ _ h; simp at h
  | @step t t1 t2 e0 rest o hl he hrest ih =>
    intro n d dn e' hOkd hland hW hafter hn
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
      rcases hS d e0 hOkd ins hg1.1 hg1.2 hc hq1 hW0 hf with
        ⟨d1, t', hn1, hl', hg', hq'⟩ | ⟨hn1, -⟩
      · have hafter' : C.toMachine.after (some d1) (rest.take n) = some (some dn) := by
          change (C.next d e0).bind _ = _ at hafter
          rw [hn1] at hafter
          exact hafter
        exact ih (hOk d e0 d1 hOkd hW0 hn1) ⟨t', hl', hg', hq'⟩ hW hafter' hn
      · change (C.next d e0).bind _ = _ at hafter
        rw [hn1] at hafter
        cases hafter
  | @last t t1 e hl he =>
    intro n d dn e' hOkd hland hW hafter hn
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

/-- **The strict chain after a UB-tolerant prefix.** The machine follows the run from `u`
tolerantly to the state `dk0` before event `k0`, where the invariant holds by the state alone
(`hQ0`); from there the steps are strict (`strictQ_from`) up to event `k0 + m + 1`. -/
theorem strictQ_window (hC : C.SoundU) {Q : TState → Prop} {Wf : Event → Prop} {Ok : C.D → Prop}
    (hS : ∀ d e, Ok d → C.StepForQ Q Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → C.next d e = some (some d') → Ok d')
    {u : TState} {es : List Event} {o : Option TState} (hr : Run K A L g u es o) :
    ∀ {k0 m : Nat} {d dk0 dn : C.D} {e' : Event}, C.toMachineU.Reach (some d) u →
      C.toMachine.after (some d) (es.take k0) = some (some dk0) → Ok dk0 →
      (∀ t, C.Good (some dk0) t → Q t) → (∀ e ∈ (es.drop k0).take (m + 1), Wf e) →
      C.toMachine.after (some dk0) ((es.drop k0).take (m + 1)) = some (some dn) →
      es[k0 + (m + 1)]? = some e' →
      Ok dn ∧ ∃ t1 o', C.Good (some dn) t1 ∧ Q t1 ∧ EStep K A L g t1 e' o' := by
  induction hr with
  | nil t => intro k0 m d dk0 dn e' _ _ _ _ _ _ h; simp at h
  | @step t t1 t2 e0 rest o hl he hrest ih =>
    intro k0 m d dk0 dn e' hreach hafter hOkd hQ0 hW hafter2 hn
    have hg := hreach t1 hl (stops_of_estep he)
    have hgood : C.Good (some d) t1 := good_of_goodU_fires hg he
    cases k0 with
    | zero =>
      rw [List.take_zero] at hafter
      change some (some d) = some (some dk0) at hafter
      obtain rfl := Option.some.inj (Option.some.inj hafter)
      simp only [List.drop_zero, Nat.zero_add] at hW hafter2 hn
      exact strictQ_from hC hS hOk (Run.step hl he hrest) hOkd ⟨t1, hl, hgood, hQ0 t1 hgood⟩
        hW hafter2 hn
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
          exact ih hreach' hafter hOkd hQ0 hW hafter2 hn
        · have hn'' : C.next d e0 = none := hn'
          rw [hq] at hn''; cases hn''
  | @last t t1 e hl he =>
    intro k0 m d dk0 dn e' hreach hafter hOkd hQ0 hW hafter2 hn
    cases k0 with
    | zero => simp at hn
    | succ k => rw [Nat.succ_add] at hn; simp at hn

variable {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}
  {back : (i : ι) → (R i).D → Option P.D}

theorem counted_stepForQ {κ : Type} {cls : κ → Event → Bool} {Q : TState → Prop}
    {Wf : Event → Prop} {d : C.D} {e : Event} (h : C.StepForQ Q Wf d e) (n : κ → Nat) :
    (C.counted cls).StepForQ Q Wf (d, n) e := by
  intro t u ins hat hinv hc hq hw hf
  rcases h ins hat hinv hc hq hw hf with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨(d', bump cls n e), t', by rw [counted_next, hn]; rfl, hl, hg, hq'⟩
  · exact .inr ⟨by rw [counted_next, hn]; rfl, hd⟩

theorem glue_inl_stepForQ {Q : TState → Prop} {Wf : Event → Prop} {d : P.D} {e : Event}
    (hP : exit d = none → P.StepForQ Q Wf d e) (hglue : Handoff P R exit) :
    (glue P R exit).StepForQ Q Wf (.inl d) e := by
  intro t u ins hat hinv hc hq hw hf
  rcases hP hinv.2 ins hat hinv.1 hc hq hw hf with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl, hl,
      good_enter hglue hg, hq'⟩
  · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩

theorem glue_inr_stepForQ {Q : TState → Prop} {Wf : Event → Prop} {i : ι} {d : (R i).D}
    {e : Event} (h : (R i).StepForQ Q Wf d e) : (glue P R exit).StepForQ Q Wf (.inr ⟨i, d⟩) e := by
  intro t u ins hat hinv hc hq hw hf
  rcases h ins hat hinv hc hq hw hf with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨.inr ⟨i, d'⟩, t', by show ((R i).next d e).map _ = _; rw [hn]; rfl, hl, hg, hq'⟩
  · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩

theorem loopGlue_inl_stepForQ {Q : TState → Prop} {Wf : Event → Prop} {d : P.D} {e : Event}
    (hP : exit d = none → P.StepForQ Q Wf d e) (hglue : Handoff P R exit)
    (hinit : ∀ i, back i (R i).init = none) :
    (loopGlue P R exit back).StepForQ Q Wf (.inl d) e := by
  intro t u ins hat hinv hc hq hw hf
  rcases hP hinv.2 ins hat hinv.1 hc hq hw hf with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl, hl,
      good_enter_loop hglue hinit hg, hq'⟩
  · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩

theorem loopGlue_inr_stepForQ {Q : TState → Prop} {Wf : Event → Prop} {i : ι} {d : (R i).D}
    {e : Event} (hR : back i d = none → (R i).StepForQ Q Wf d e) (hglue : Handoff P R exit)
    (hback : Back P R back) (hinit : ∀ i, back i (R i).init = none) :
    (loopGlue P R exit back).StepForQ Q Wf (.inr ⟨i, d⟩) e := by
  intro t u ins hat hinv hc hq hw hf
  rcases hR hinv.2 ins hat hinv.1 hc hq hw hf with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨backEnter P R exit back i d', t',
      by show ((R i).next d e).map _ = _; rw [hn]; rfl, hl,
      good_backEnter hglue hback hinit hg, hq'⟩
  · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩

end

end PTX.Flow.Code
