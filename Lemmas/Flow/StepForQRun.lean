-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQPc

@[expose] public section

/-! # The strict chain, with the run's own states

`strictQ_fromPc` forgets which states of the run it speaks of. `strictQ_fromPcRun` also returns
the run's state `t0` before the event `n`'s local steps, the state `t1` that fires it, and the run
up to `t0`: the invariant and strict goodness are facts about the run's own state. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **The strict chain with the run's states.** -/
theorem strictQ_fromPcRun (hC : C.SoundU) {Q : TState → Prop} {Wf : Event → Prop}
    {Ok : C.D → Prop} (hS : ∀ d e, Ok d → C.StepForQ Q Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = C.pc d → C.next d e = some (some d') → Ok d')
    {t : TState} {es : List Event} {o : Option TState} (hr : Run K A L g t es o) :
    ∀ {n : Nat} {d dn : C.D} {e' : Event}, Ok d →
      (∃ t1, Relation.ReflTransGen (Tau K A L g) t t1 ∧ C.Good (some d) t1 ∧ Q t1) →
      (∀ e ∈ es.take n, Wf e) → C.toMachine.after (some d) (es.take n) = some (some dn) →
      es[n]? = some e' →
      Ok dn ∧ ∃ t0 t1 o', Run K A L g t (es.take n) (some t0) ∧
        Relation.ReflTransGen (Tau K A L g) t0 t1 ∧ C.Good (some dn) t1 ∧ Q t1 ∧
        EStep K A L g t1 e' o' := by
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
      exact ⟨hOkd, t, _, _, Run.nil t, hl, hg1, hq1, he⟩
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
        obtain ⟨hok, t0, t1', o', hrun, hs, hg2, hq2, hes⟩ :=
          ih (hOk d e0 d1 hOkd hW0 (fires_pc hf) hn1) ⟨t', hl', hg', hq'⟩ hW hafter' hn
        exact ⟨hok, t0, t1', o', by rw [List.take_succ_cons]; exact Run.step hl he hrun, hs,
          hg2, hq2, hes⟩
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
      exact ⟨hOkd, t, _, _, Run.nil t, hl, hg1, hq1, he⟩
    | succ n => simp at hn

/-- **The strict chain from the thread's first state**, with the run's states. -/
theorem strictQ_fromInit (hC : C.SoundU) {Q : TState → Prop} {Wf : Event → Prop}
    {Ok : C.D → Prop} (hS : ∀ d e, Ok d → C.StepForQ Q Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = C.pc d → C.next d e = some (some d') → Ok d')
    {es : List Event} {o : Option TState} (hr : Run K A L g {} es o) (hOk0 : Ok C.init)
    (hQ0 : ∀ t, C.Good (some C.init) t → Q t) {n : Nat} (hpos : 0 < n) {dn : C.D} {e' : Event}
    (hW : ∀ e ∈ es.take n, Wf e) (hafter : C.toMachine.after (some C.init) (es.take n) =
      some (some dn)) (hn : es[n]? = some e') :
    Ok dn ∧ ∃ t0 t1 o', Run K A L g {} (es.take n) (some t0) ∧
      Relation.ReflTransGen (Tau K A L g) t0 t1 ∧ C.Good (some dn) t1 ∧ Q t1 ∧
      EStep K A L g t1 e' o' := by
  cases hr with
  | nil => simp at hn
  | @step t t1 t2 e0 rest o hl he hrest =>
    have hg := reach_init hC t1 hl (stops_of_estep he)
    have hgood : C.Good (some C.init) t1 := good_of_goodU_fires hg he
    exact strictQ_fromPcRun hC hS hOk (Run.step hl he hrest) hOk0 ⟨t1, hl, hgood, hQ0 t1 hgood⟩
      hW hafter hn
  | @last t t1 e0 hl he =>
    cases n with
    | zero => omega
    | succ n => simp at hn

end

end PTX.Flow.Code
