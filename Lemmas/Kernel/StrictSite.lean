-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame
public import Lemmas.Flow.StrictWindow

@[expose] public section

/-! # An event at a followed state fires from a strictly good concrete state

A thread machine sound only through final undefined behaviour (`Code.SoundU`) fires every
event but the last from a strictly good state (`Code.good_of_goodU_fires`). `strict_site`: the
concrete state before event `k` of a followed thread is strictly good (`Code.Good`) at the state
`σ` the machine is in when the step before it is strict for the event it took (`Code.StepFor`);
at the first event the start's goodness suffices. The conclusion is the site instruction and the
template its event is fired from, with no fault alternative. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {C : ∀ g, Code K A L g}
  {mem0 : Mem0} {X : Execution} {g k : Nat}

/-- **An event at a followed state fires from a strictly good concrete state** when the step into
the state is strict for its event. -/
theorem strict_site (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X)
    {e : Event} {σ : (C g).D} (he : X.get (g, k) = some e)
    (hσ : stateAt C X g k = some (some σ))
    (hprev : ∀ j dj ej, j + 1 = k → (X.tr g)[j]? = some ej →
      stateAt C X g j = some (some dj) → (C g).next dj ej = some (some σ) →
      (C g).StepFor dj ej) :
    ∃ t o ins, (C g).Good (some σ) t ∧ K.code[(C g).pc σ]? = some ins ∧
      Fires ((C g).pc σ) (eventTmpl A L g t ins.op) e o := by
  have hg := lt_of_get hX he
  obtain ⟨o0, hr⟩ := hX.thr g hg
  have hcore : ∃ t o', (C g).Good (some σ) t ∧ EStep K A L g t e o' := by
    cases k with
    | zero =>
      rw [stateAt_zero] at hσ
      obtain rfl := Option.some.inj (Option.some.inj hσ)
      have he0 : (X.tr g)[0]? = some e := he
      cases hl : X.tr g with
      | nil => rw [hl] at he0; simp at he0
      | cons a rest =>
        rw [hl] at he0 hr
        simp only [List.getElem?_cons_zero, Option.some.injEq] at he0
        subst he0
        exact Code.strict_first (hC g hg) hr rfl
    | succ j =>
      have hlen := (List.getElem?_eq_some_iff.mp (show (X.tr g)[j + 1]? = some e from he)).1
      obtain ⟨ej, hej⟩ : ∃ ej, (X.tr g)[j]? = some ej :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [stateAt_succ hej] at hσ
      rcases hs : stateAt C X g j with _ | _ | dj
      · rw [hs] at hσ; cases hσ
      · rw [hs] at hσ; cases hσ
      · rw [hs] at hσ
        have hn : (C g).next dj ej = some (some σ) := hσ
        exact Code.strict_window (hC g hg) hr (Code.reach_init (hC g hg)) hej he
          hs hn (hprev j dj ej rfl hej hs hn)
  obtain ⟨t, o', hgd, hes⟩ := hcore
  obtain ⟨ins, hc, hf⟩ := Code.fired_of_good (hC g hg) hgd hes
  exact ⟨t, o', ins, hgd, hc, hf⟩

end
end PTX.Frame
