-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Interface

@[expose] public section

/-! # `copy_ldg`: the events of an execution

Every event of a consistent execution is the read of `A[g]` as its thread's first event, the
write of the word read to `B[g]` as its second, the exit, or the undefined behaviour of a
thread that read bytes it cannot store. -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

theorem take_eq_nil {es : List Event} {k : Nat} {e : Event} (hk : es[k]? = some e)
    (h : es.take k = []) : k = 0 := by
  have hl := (List.getElem?_eq_some_iff.mp hk).1
  have := congrArg List.length h
  simp only [List.length_take, List.length_nil] at this
  omega

theorem take_eq_singleton {es : List Event} {k : Nat} {e a : Event} (hk : es[k]? = some e)
    (h : es.take k = [a]) : k = 1 ∧ es[0]? = some a := by
  have hl := (List.getElem?_eq_some_iff.mp hk).1
  have hlen := congrArg List.length h
  simp only [List.length_take, List.length_singleton] at hlen
  have hk1 : k = 1 := by omega
  subst hk1
  refine ⟨rfl, ?_⟩
  have : (es.take 1)[0]? = some a := by rw [h]; rfl
  simpa [List.getElem?_take] using this

theorem take_eq_pair {es : List Event} {k : Nat} {e a b : Event} (hk : es[k]? = some e)
    (h : es.take k = [a, b]) : k = 2 ∧ es[0]? = some a ∧ es[1]? = some b := by
  have hl := (List.getElem?_eq_some_iff.mp hk).1
  have hlen := congrArg List.length h
  simp only [List.length_take, List.length_cons, List.length_nil] at hlen
  have hk2 : k = 2 := by omega
  subst hk2
  refine ⟨rfl, ?_, ?_⟩
  · have : (es.take 2)[0]? = some a := by rw [h]; rfl
    simpa [List.getElem?_take] using this
  · have : (es.take 2)[1]? = some b := by rw [h]; rfl
    simpa [List.getElem?_take] using this

/-- **The events of a possible execution.** -/
theorem event_cases (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X) {e : EvId} {ev : Event} (h : X.get e = some ev) :
    e.1 < L.threads ∧
      ((e.1 < N ∧ e.2 = 0 ∧ ∃ bs, bs.length = 4 ∧ ev = ncE A e.1 bs) ∨
       (e.1 < N ∧ e.2 = 1 ∧ ∃ bs v, bs.length = 4 ∧ rebuild 3 bs = .ok v ∧ v.bytes = 4 ∧
          X.get (e.1, 0) = some (ncE A e.1 bs) ∧ ev = wrE B e.1 v) ∨
       (ev = exE ∧ ((e.2 = 0 ∧ N ≤ e.1) ∨
          (e.2 = 2 ∧ e.1 < N ∧ ∃ bs v, bs.length = 4 ∧ rebuild 3 bs = .ok v ∧ v.bytes = 4 ∧
            X.get (e.1, 0) = some (ncE A e.1 bs) ∧ X.get (e.1, 1) = some (wrE B e.1 v)))) ∨
       (e.1 < N ∧ (∃ f, ev.kind = .ub f) ∧ ∃ bs, bs.length = 4 ∧
          X.get (e.1, 0) = some (ncE A e.1 bs) ∧ ∀ v, rebuild 3 bs = .ok v → v.bytes ≠ 4)) := by
  obtain ⟨g, k⟩ := e
  have hg := Frame.lt_of_get hX h
  refine ⟨hg, ?_⟩
  simp only at hg ⊢
  have hh : (X.tr g)[k]? = some ev := h
  rcases Frame.fired (sound_all hpre) hX h with ⟨σ, o, hs, -⟩ | ⟨hs, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hs (ht.tracked g k hg)
    | some d =>
      have hsite := ht.site_event h hs
      have hrun := ht.run_facts hg hs
      cases d with
      | load =>
        obtain ⟨hl0, hgN⟩ := hrun
        obtain ⟨bs, hl, rfl⟩ := hsite
        exact .inl ⟨hgN, take_eq_nil hh hl0, bs, hl, rfl⟩
      | store v =>
        obtain ⟨bs, hl, hv, hpre', hgN⟩ := hrun
        obtain ⟨hk1, h0⟩ := take_eq_singleton hh hpre'
        rcases hsite with ⟨hb, rfl⟩ | ⟨hb, f, rfl⟩
        · exact .inr (.inl ⟨hgN, hk1, bs, v, hl, hv, hb, h0, rfl⟩)
        · refine .inr (.inr (.inr ⟨hgN, ⟨f, rfl⟩, bs, hl, h0, fun v' hv' => ?_⟩))
          rw [hv] at hv'
          cases hv'
          exact hb
      | exit =>
        subst hsite
        rcases hrun with ⟨hl0, hNg⟩ | ⟨bs, v, hl, hv, hb, hpre', hgN⟩
        · exact .inr (.inr (.inl ⟨rfl, .inl ⟨take_eq_nil hh hl0, hNg⟩⟩))
        · obtain ⟨hk2, h0, h1⟩ := take_eq_pair hh hpre'
          exact .inr (.inr (.inl ⟨rfl, .inr ⟨hk2, hgN, bs, v, hl, hv, hb, h0, h1⟩⟩))
  · obtain ⟨-, hgN, bs, hl, hv, ht'⟩ := ht.dead_ub h hs
    obtain ⟨hk1, h0⟩ := take_eq_singleton hh ht'
    exact .inr (.inr (.inr ⟨hgN, ⟨f, rfl⟩, bs, hl, h0, fun v hv' => absurd hv' (hv v)⟩))

end
end PTX.Kernels.CopyLdg.Proof
