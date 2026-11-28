-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.FrameU
public import Lemmas.Flow.Determinism

@[expose] public section

/-! # The state before an event and the state after it

A lane's run up to and including the event `e` (the trace `take (k + 1)`) ends in the state `t0`
after the event. The state `s` at which the event fired is the next stop of the run of the first
`k` events, so the machine's state after `k` events describes it (`Frame.post_event`): the lane's
own state at the event, with the machine's facts, not a state that merely fires an event like it. -/

namespace PTX.Flow
open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A run of a trace with a last event is a run of the rest, local steps and that event. -/
theorem Run.unsnoc : ∀ (l : List Event) (e : Event) {t : TState} {o : Option TState},
    Run K A L g t (l ++ [e]) o → ∃ u s, Run K A L g t l (some u) ∧
      Relation.ReflTransGen (Tau K A L g) u s ∧ EStep K A L g s e o
  | [], e, t, o, h => by
    generalize hx : ([] ++ [e] : List Event) = x at h
    cases h with
    | nil => simp at hx
    | step hl he hr =>
      simp only [List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      cases hr
      exact ⟨t, _, .nil t, hl, he⟩
    | last hl he =>
      simp only [List.nil_append, List.cons.injEq, and_true] at hx
      subst hx
      exact ⟨t, _, .nil t, hl, he⟩
  | e0 :: rest, e, t, o, h => by
    generalize hx : (e0 :: rest) ++ [e] = x at h
    cases h with
    | nil => simp at hx
    | step hl he hr =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨u, s, h1, h2, h3⟩ := Run.unsnoc rest e hr
      exact ⟨u, s, .step hl he h1, h2, h3⟩
    | last hl he =>
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff, List.cons_ne_self,
        and_false] at hx

end PTX.Flow

namespace PTX.Frame
open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Code K A L g} {g k : Nat}

/-- **The state at which the event `k` fired** is the machine's state after `k` events: the lane's
run to the state after the event passes through a state with the machine's facts. -/
theorem post_event (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X)
    {e : Event} (he : X.get (g, k) = some e) {t0 : TState} {d : (C g).D}
    (hr : Run K A L g {} ((X.tr g).take (k + 1)) (some t0))
    (hσ : stateAt C X g k = some (some d)) :
    ∃ s ins, (C g).AtD d s ∧ (C g).inv d ∧ K.code[(C g).pc d]? = some ins ∧
      EStep K A L g s e (some t0) := by
  have hg : g < L.threads := lt_of_get hX he
  have hk : (X.tr g)[k]? = some e := he
  rw [List.take_add_one, hk] at hr
  obtain ⟨u, s, hru, hs, hes⟩ := Run.unsnoc _ e hr
  obtain ⟨s', hl, hgood⟩ := Code.end_siteU (hC g hg) hru hσ
  have hstop : Stops K A L g s := stops_of_estep hes
  rcases hgood with hgd | ⟨f, hf⟩
  · obtain ⟨ins, hc, ho⟩ := Code.site_outU ((hC g hg).steps d) hgd
    have : s' = s := stop_unique hl hs ⟨_, ho⟩ hstop
    subst this
    exact ⟨s', ins, hgd.1, hgd.2, hc, hes⟩
  · have : s' = s := stop_unique hl hs ⟨_, hf⟩ hstop
    subst this
    obtain ⟨m, hm, hfire⟩ := hes
    rw [hf] at hm
    cases hm
    exact absurd hfire.2 (by simp)

end PTX.Frame
