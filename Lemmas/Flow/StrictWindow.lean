-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Counted

@[expose] public section

/-! # A strict step inside a UB-tolerant machine

A machine that is sound only through final undefined behaviour (`Code.SoundU`) may still prove a
state's step obligation strictly, for one event (`StepFor`). The concrete state before the next
event is then a good state in the strict sense (`Code.Good`), not the fault alternative of `GoodU`:

* an event that continues the thread (`o = some u`) never fires from the fault alternative
  (`good_of_goodU_fires`), so the state before every event but the last is strictly good;
* `strict_window`: if the step of the state before event `k` is strict for that event, the state
  before event `k + 1` is strictly good, by the uniqueness of the first stopping state
  (`stop_unique`);
* `strict_first`: the state before the first event is strictly good (`SoundU.start`). -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The strict step obligation of one state for one event. -/
def StepFor (C : Code K A L g) (d : C.D) (e : Event) : Prop :=
  ∀ {t u : TState} (ins : Instr), C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
    Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) →
    (C.next d e = some none ∨
      ∃ d' t', C.next d e = some (some d') ∧ Relation.ReflTransGen (Tau K A L g) u t' ∧
        C.Good (some d') t') ∨
    (C.next d e = none ∧ Machine.Dead (K := K) (A := A) (L := L) (g := g) u)

theorem StepAt.stepFor {d : C.D} (h : C.StepAt d) (e : Event) : C.StepFor d e :=
  fun ins ha hi hc hf => h.step ins ha hi hc hf

/-- A state that fires an event that continues the thread is strictly good. -/
theorem good_of_goodU_fires {d : C.D} {t u : TState} {e : Event} (h : C.GoodU (some d) t)
    (he : EStep K A L g t e (some u)) : C.Good (some d) t := by
  rcases h with h | ⟨f, hf⟩
  · exact h
  · obtain ⟨m, hm, hfire⟩ := he
    rw [hf] at hm
    cases hm
    simp [Fires] at hfire

theorem stops_of_good (hC : C.SoundU) {d : C.D} {t : TState} (h : C.Good (some d) t) :
    Stops K A L g t := by
  obtain ⟨ins, -, ho⟩ := site_outU (hC.steps d) h
  exact ⟨_, ho⟩

/-- The event fired by a strictly good state is its site's template's. -/
theorem fired_of_good (hC : C.SoundU) {d : C.D} {t : TState} (h : C.Good (some d) t)
    {e : Event} {o : Option TState} (he : EStep K A L g t e o) :
    ∃ ins, K.code[C.pc d]? = some ins ∧ Fires (C.pc d) (eventTmpl A L g t ins.op) e o := by
  obtain ⟨ins, hc, ho⟩ := site_outU (hC.steps d) h
  obtain ⟨m, hm, hf⟩ := he
  rw [ho] at hm
  cases hm
  exact ⟨ins, hc, h.1.1 ▸ hf⟩

/-- **The strict window**: along a run whose state before event `k` is `dk`, if the step of `dk`
for event `k` is strict and reaches `d'`, a state that fires event `k + 1` is strictly good. -/
theorem strict_window (hC : C.SoundU) {u : TState} {es : List Event} {o : Option TState}
    (hr : Run K A L g u es o) :
    ∀ {k : Nat} {d dk d' : C.D} {ek e' : Event},
      C.toMachineU.Reach (some d) u → es[k]? = some ek → es[k + 1]? = some e' →
      C.toMachine.after (some d) (es.take k) = some (some dk) →
      C.next dk ek = some (some d') → C.StepFor dk ek →
      ∃ t o', C.Good (some d') t ∧ EStep K A L g t e' o' := by
  induction hr with
  | nil t => intro k d dk d' ek e' _ h; simp at h
  | @step t t1 t2 e0 rest o hl he hrest ih =>
    intro k d dk d' ek e' hreach hek he' hafter hnext hfor
    have hg := hreach t1 hl (stops_of_estep he)
    have hgood : C.Good (some d) t1 := good_of_goodU_fires hg he
    cases k with
    | zero =>
      simp only [List.take_zero] at hafter
      obtain rfl := Option.some.inj (Option.some.inj hafter)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hek
      subst hek
      obtain ⟨ins, hc, hf⟩ := fired_of_good hC hgood he
      rcases hfor ins hgood.1 hgood.2 hc hf with (hn | ⟨d'', t', hn, hl', hg'⟩) | ⟨hn, -⟩
      · rw [hnext] at hn; cases hn
      · rw [hnext] at hn
        obtain rfl := Option.some.inj (Option.some.inj hn)
        cases hrest with
        | nil => simp at he'
        | step hl2 he2 _ =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at he'
          subst he'
          obtain rfl := stop_unique hl2 hl' (stops_of_estep he2) (stops_of_good hC hg')
          obtain ⟨m, hm, hf2⟩ := he2
          exact ⟨_, _, hg', m, hm, hf2⟩
        | last hl2 he2 =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at he'
          subst he'
          obtain rfl := stop_unique hl2 hl' (stops_of_estep he2) (stops_of_good hC hg')
          obtain ⟨m, hm, hf2⟩ := he2
          exact ⟨_, _, hg', m, hm, hf2⟩
      · rw [hnext] at hn; cases hn
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
        obtain ⟨m, hm, hf⟩ := he
        have hout := hC.machine.out_eq hg
        have hf' : Fires t1.pc (C.toMachineU.tmpl (some d) t1) e0 (some t2) := by
          have : C.toMachineU.tmpl (some d) t1 = m := by
            simp only [toMachineU, tmpl, hm]
          rw [this]; exact hf
        rcases hC.machine.step hg hf' with ⟨σ', hn, hreach'⟩ | ⟨hn, -⟩
        · have hn' : C.next d e0 = some σ' := hn
          rw [hq] at hn'
          obtain rfl := Option.some.inj hn'
          rw [List.getElem?_cons_succ] at hek he'
          exact ih hreach' hek he' hafter hnext hfor
        · have hn' : C.next d e0 = none := hn
          rw [hq] at hn'; cases hn'
  | last hl he => intro k d dk d' ek e' _ hek he'; cases k <;> simp at he'

/-- **The first event**: the state before it is strictly good. -/
theorem strict_first (hC : C.SoundU) {es : List Event} {o : Option TState}
    (hr : Run K A L g {} es o) {e0 : Event} {rest : List Event} (h : es = e0 :: rest) :
    ∃ t o', C.Good (some C.init) t ∧ EStep K A L g t e0 o' := by
  obtain ⟨t0, hl0, ha, hi⟩ := hC.start
  subst h
  have hg0 : C.Good (some C.init) t0 := ⟨ha, hi⟩
  cases hr with
  | step hl he _ =>
    obtain rfl := stop_unique hl hl0 (stops_of_estep he) (stops_of_good hC hg0)
    exact ⟨_, _, hg0, he⟩
  | last hl he =>
    obtain rfl := stop_unique hl hl0 (stops_of_estep he) (stops_of_good hC hg0)
    exact ⟨_, _, hg0, he⟩

/-- The machine's reach of its first state, from its start. -/
theorem reach_init (hC : C.SoundU) : C.toMachineU.Reach (some C.init) {} := by
  obtain ⟨t0, hl0, ha, hi⟩ := hC.start
  intro t hl hs
  have hg0 : C.Good (some C.init) t0 := ⟨ha, hi⟩
  obtain rfl := stop_unique hl hl0 hs (stops_of_good hC hg0)
  exact .inl hg0

end
end PTX.Flow.Code
