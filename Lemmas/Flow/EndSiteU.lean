-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.EndSite
public import Lemmas.Flow.CodeU

@[expose] public section

namespace PTX.Flow.Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- Control tracking uses exactly the same prefix fold as strict tracking. -/
theorem after_eqU (σ : Option C.D) (es : List Event) :
    C.toMachineU.after σ es = C.toMachine.after σ es := by
  induction es generalizing σ with
  | nil => rfl
  | cons e es ih =>
    change (C.toMachine.next σ e).bind (fun s => C.toMachineU.after s es) =
      (C.toMachine.next σ e).bind (fun s => C.toMachine.after s es)
    cases C.toMachine.next σ e with
    | none => rfl
    | some σ' => exact ih σ'

theorem fired_siteU (hC : C.SoundU) {d : C.D} {e : Event} {o : Option TState}
    (hf : C.toMachineU.Fired (some d) e o) (hu : ∀ f, e.kind ≠ .ub f) :
    ∃ t ins, C.AtD d t ∧ C.inv d ∧ K.code[C.pc d]? = some ins ∧
      Fires (C.pc d) (eventTmpl A L g t ins.op) e o := by
  obtain ⟨t, hg, hf⟩ := hf
  change Fires t.pc (C.tmpl none t) e o at hf
  rcases hg with hg | ⟨f, ho⟩
  · obtain ⟨ins, hc, ho⟩ := site_outU (hC.steps d) hg
    exact ⟨t, ins, hg.1, hg.2, hc, by simpa only [tmpl, ho, hg.1.1] using hf⟩
  · simp only [tmpl, ho] at hf
    exact absurd (congrArg Event.kind hf.1) (hu f)

theorem end_site_fromU (hC : C.SoundU) {es : List Event} {t u : TState} {d d' : C.D}
    (hg : ∃ s, Relation.ReflTransGen (Tau K A L g) t s ∧ C.GoodU (some d) s)
    (hr : Run K A L g t es (some u)) (ha : C.toMachine.after (some d) es = some (some d')) :
    ∃ s, Relation.ReflTransGen (Tau K A L g) u s ∧ C.GoodU (some d') s := by
  generalize ho : some u = o at hr
  induction hr generalizing d with
  | nil =>
    cases ho
    cases ha
    exact hg
  | step hl he _ ih =>
    obtain ⟨s, hs, hg⟩ := hg
    obtain ⟨m, hm, hf⟩ := he
    cases stop_unique hl hs ⟨m, hm⟩ ⟨_, out_eq_stepsU hC.steps hg⟩
    rcases hg with hg | ⟨f, hb⟩
    · obtain ⟨ins, hc, hout⟩ := site_outU (hC.steps d) hg
      rw [hout] at hm
      cases hm
      rw [hg.1.1] at hf
      change (C.next d _).bind _ = _ at ha
      rcases (hC.steps d).step ins hg.1 hg.2 hc hf with (hn | ⟨_, s, hn, hl', hg'⟩) | ⟨hn, _⟩
      · rw [hn] at ha
        change C.toMachine.after none _ = _ at ha
        rw [after_none] at ha
        cases ha
      · rw [hn] at ha
        exact ih ⟨s, hl', hg'⟩ ha ho
      · rw [hn] at ha
        cases ha
    · rw [hb] at hm
      cases hm
      cases hf.2
  | last => cases ho

theorem end_siteU (hC : C.SoundU) {es : List Event} {u : TState} {d : C.D}
    (hr : Run K A L g {} es (some u)) (ha : C.toMachine.after (some C.init) es = some (some d)) :
    ∃ s, Relation.ReflTransGen (Tau K A L g) u s ∧ C.GoodU (some d) s := by
  obtain ⟨t, hl, hg⟩ := hC.start
  exact end_site_fromU hC ⟨t, hl, Or.inl hg⟩ hr ha

end PTX.Flow.Code
