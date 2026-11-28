-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.NoUbStrictQLane
public import Lemmas.Flow.StepForQPcP

@[expose] public section

/-! # The strict window of a lane, with a fact about the lane's own states

`Frame.noUb_strictQ_lane` (`Lemmas/Kernel/NoUbStrictQLane.lean`) for steps that may use `P u` of
the state `u` after their event (`Code.StepForQP`), where `P` follows from `u` being a state of
the lane's own run (`LaneAt`): a fact such as the ideal rule not declining holds of the states the
lane reaches, and not of every state. -/

namespace PTX.Frame

open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : ∀ g, Code K A L g} {J : ∀ g, (C g).D → Prop} {X : Execution}

/-- A state between two events of the thread `g` of the execution `X`. -/
def LaneAt (K : Kernel) (A : List Assumption) (L : Launch) (X : Execution) (g : Nat)
    (t : TState) : Prop :=
  ∃ k t0, Run K A L g {} ((X.tr g).take k) (some t0) ∧ Relation.ReflTransGen (Tau K A L g) t0 t

/-- The position invariant of the lane's run: the remaining events are the trace after `k`. -/
def LanePos (K : Kernel) (A : List Assumption) (L : Launch) (X : Execution) (g : Nat)
    (t : TState) (es : List Event) : Prop :=
  ∃ k t0, Run K A L g {} ((X.tr g).take k) (some t0) ∧ es = (X.tr g).drop k ∧
    Relation.ReflTransGen (Tau K A L g) t0 t

theorem lanePos_step {g : Nat} {P : TState → Prop} (hP : ∀ t, LaneAt K A L X g t → P t) :
    Code.PosStep (K := K) (A := A) (L := L) (g := g) (LanePos K A L X g) P := by
  intro t t1 t2 e0 rest ⟨k, t0, hr, hes, hl0⟩ hl he
  have hdrop : (X.tr g).drop k = e0 :: rest := hes.symm
  have hk : (X.tr g)[k]? = some e0 := by
    have h0 : ((X.tr g).drop k)[0]? = some e0 := by rw [hdrop]; rfl
    simpa using h0
  have hr' : Run K A L g {} ((X.tr g).take (k + 1)) (some t2) := by
    rw [List.take_add_one, hk]
    exact Run.snoc hr (hl0.trans hl) he
  refine ⟨⟨k + 1, t2, hr', ?_, .refl⟩, hP t2 ⟨k + 1, t2, hr', .refl⟩⟩
  rw [← List.drop_drop, hdrop]
  rfl

/-- **A lane has no undefined-behaviour event at the end of a strict window**, the steps using
`P` of the lane's own states. -/
theorem noUb_strictQP_lane (hC : ∀ g < L.threads, (C g).SoundU)
    (hX : Consistent L K A mem0 X) {g : Nat} (hF : ∀ k, FollowedAt C J X g k)
    {Q P : TState → Prop} {Wf : Event → Prop} {Ok : (C g).D → Prop}
    (hP : ∀ t, LaneAt K A L X g t → P t)
    (hS : ∀ d e, Ok d → (C g).StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = (C g).pc d → (C g).next d e = some (some d') →
      Ok d')
    {k0 m : Nat} {dk0 : (C g).D} (h0 : stateAt C X g k0 = some (some dk0)) (hOk0 : Ok dk0)
    (hQ0 : ∀ t, (C g).Good (some dk0) t → Q t) {e : Event}
    (he : X.get (g, k0 + (m + 1)) = some e)
    (hW : ∀ j, k0 ≤ j → j < k0 + (m + 1) → ∀ ej, X.get (g, j) = some ej → Wf ej)
    (safe : ∀ σ t ins, stateAt C X g (k0 + (m + 1)) = some (some σ) → Ok σ → J g σ →
      e.pc = (C g).pc σ → (C g).Good (some σ) t → Q t → K.code[(C g).pc σ]? = some ins →
      ∀ f, eventTmpl A L g t ins.op ≠ .ub f)
    (live : ∀ i d v, k0 ≤ i → i < k0 + (m + 1) → Ok d → X.get (g, i) = some v →
      stateAt C X g i = some (some d) → J g d → NoUbBefore X g (i + 1) →
      (C g).next d v = none → v.kind = .exit) (f : Fault) : e.kind ≠ .ub f := by
  intro hk
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
    refine Code.strictQP_windowPc (hC g hg) hS hOk (lanePos_step hP) hr
      ⟨0, {}, by simpa using Run.nil _, by simp, .refl⟩ (Code.reach_init (hC g hg)) (by
      unfold stateAt at h0; exact h0) hOk0 hQ0 (fun ej hej => ?_) hd ?_
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hej
      rw [List.getElem?_take] at hj
      split_ifs at hj with hjn
      rw [List.getElem?_drop] at hj
      exact hW (k0 + j) (by omega) (by omega) _ hj
    · simpa using hen
  cases hs : stateAt C X g (k0 + (m + 1)) with
  | some o =>
    cases o with
    | some σ =>
      obtain ⟨hOkσ, t1, o', hgd, hq, hes⟩ := window (k0 + (m + 1)) σ e (by omega) le_rfl hs he
      obtain ⟨ins, hc, hfire⟩ := Code.fired_of_good (hC g hg) hgd hes
      have hu := fires_ub hfire hk
      exact safe σ t1 ins hs hOkσ ((hF _).2 σ hs) (EventFrame.fires_source_pc hfire) hgd hq hc f hu
    | none => exact (hF _).1 hs
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
