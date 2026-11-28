-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.StrictQPRunAt

@[expose] public section

/-! # A strict window that ends at an event: the lane's state and stop state there

`Frame.noUb_strictQPRun_lane` for an event that may be anything: the machine's state before the
event is not lost (the window's states die only on the exit), is `Ok`, and the stop state at which
the event fires has the machine's facts and the window's invariant. -/

namespace PTX.Frame

open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : ∀ g, Code K A L g} {J : ∀ g, (C g).D → Prop} {X : Execution}

/-- **A strict window ends in a state and a stop state with the invariant.** -/
theorem strictQPRun_end (hC : ∀ g < L.threads, (C g).SoundU)
    (hX : Consistent L K A mem0 X) {g : Nat} (hF : ∀ k, FollowedAt C J X g k)
    {Q P : TState → Prop} {Wf : Event → Prop} {Ok : (C g).D → Prop}
    (hP : ∀ t, LaneAt K A L X g t → P t)
    (hS : ∀ d e, Ok d → (C g).StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = (C g).pc d → (C g).next d e = some (some d') →
      Ok d')
    {k0 m : Nat} {dk0 : (C g).D} (h0 : stateAt C X g k0 = some (some dk0)) (hOk0 : Ok dk0)
    (hQ0 : ∀ t t1, LanePos K A L X g t ((X.tr g).drop k0) →
      Relation.ReflTransGen (Tau K A L g) t t1 → (C g).Good (some dk0) t1 → Q t1) {e : Event}
    (he : X.get (g, k0 + (m + 1)) = some e)
    (hW : ∀ j, k0 ≤ j → j < k0 + (m + 1) → ∀ ej, X.get (g, j) = some ej → Wf ej)
    (live : ∀ i d v, k0 ≤ i → i < k0 + (m + 1) → Ok d → X.get (g, i) = some v →
      stateAt C X g i = some (some d) → J g d → NoUbBefore X g (i + 1) →
      (C g).next d v = none → v.kind = .exit) :
    ∃ σ, stateAt C X g (k0 + (m + 1)) = some (some σ) ∧ Ok σ ∧
      ∃ t0 t1 o', Run K A L g {} ((X.tr g).take (k0 + (m + 1))) (some t0) ∧
        Relation.ReflTransGen (Tau K A L g) t0 t1 ∧ (C g).Good (some σ) t1 ∧ Q t1 ∧
        EStep K A L g t1 e o' := by
  have nu := noUbBefore_of_get hX he
  have hg := lt_of_get hX he
  obtain ⟨o, hr⟩ := hX.thr g hg
  have hlen : ∀ n, X.get (g, n) = some e → n < (X.tr g).length := fun n h =>
    (List.getElem?_eq_some_iff.mp h).1
  -- the window lemma at an index `n` in `(k0, k0 + (m + 1)]` with a live state
  have window : ∀ n dn e', k0 < n → n ≤ k0 + (m + 1) → stateAt C X g n = some (some dn) →
      (X.tr g)[n]? = some e' → Ok dn ∧ ∃ t1 o', (C g).Good (some dn) t1 ∧ Q t1 ∧
        EStep K A L g t1 e' o' := by
    intro n dn e' hn1 hn2 hdn hen
    obtain ⟨n', rfl⟩ : ∃ n', n = k0 + (n' + 1) := ⟨n - k0 - 1, by omega⟩
    have hd := stateAt_window h0 hdn
    have hW' : ∀ ej ∈ ((X.tr g).drop k0).take (n' + 1), Wf ej := by
      intro ej hej
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hej
      rw [List.getElem?_take] at hj
      split_ifs at hj with hjn
      rw [List.getElem?_drop] at hj
      exact hW (k0 + j) (by omega) (by omega) _ hj
    obtain ⟨hok, -, t1, o', -, -, hgd, hq, hes⟩ := Code.strictQPRun_windowPc (hC g hg) hS hOk
      (lanePos_step hP) hr ⟨0, {}, by simpa using Run.nil _, by simp, .refl⟩
      (Code.reach_init (hC g hg)) (by unfold stateAt at h0; exact h0) hOk0 hQ0 hW' hd
      (by simpa using hen)
    exact ⟨hok, t1, o', hgd, hq, hes⟩
  cases hs : stateAt C X g (k0 + (m + 1)) with
  | some o =>
    cases o with
    | some σ => exact ⟨σ, rfl, strictQPRun_at hC hX hP hS hOk h0 hOk0 hQ0 (by omega) hs he hW⟩
    | none => exact ((hF _).1 hs).elim
  | none =>
    obtain ⟨i, hik, d, v, hi, hd, hn, prefixLive⟩ := first_stop_event (C := C) (g := g)
      (k := k0 + (m + 1)) (.inl hs)
    have hn' : (C g).next d v = none :=
      next_none_of_stop hi hd hn (fun h => (hF (i + 1)).1 h)
    have alive_le : ∀ j ≤ k0, ∃ d', stateAt C X g j = some (some d') := by
      intro j hj
      cases hs' : stateAt C X g j with
      | none => rw [stateAt_none_mono hs' hj] at h0; cases h0
      | some o' =>
        cases o' with
        | none => exact absurd hs' (hF j).1
        | some d' => exact ⟨d', rfl⟩
    have hik0 : k0 ≤ i := by
      by_contra hlt
      obtain ⟨a, ha⟩ := alive_le (i + 1) (by omega)
      rw [stateAt_succ hi, hd] at ha
      change (C g).next d v = _ at ha
      rw [hn'] at ha
      cases ha
    have hOkd : Ok d := by
      rcases Nat.eq_or_lt_of_le hik0 with heq | hlt
      · subst heq
        rw [h0] at hd
        obtain rfl := Option.some.inj (Option.some.inj hd)
        exact hOk0
      · exact (window i d v hlt (by omega) hd hi).1
    have hx := live i d v hik0 hik hOkd hi hd ((hF i).2 d hd) (fun u hu => nu u (by omega)) hn'
    obtain ⟨pc, kd⟩ := v
    change kd = .exit at hx
    subst hx
    have hl := Flow.Run.end_last hr hi (.inr rfl)
    have hk' : k0 + (m + 1) < (X.tr g).length := hlen _ he
    omega

end PTX.Frame
