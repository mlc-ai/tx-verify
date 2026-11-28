-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.NoUbFirstStop
public import Lemmas.Kernel.StrictSite
public import Lemmas.Kernel.Safety.TableU
public import Lemmas.Execution.EventFrameSource
public import Lemmas.Flow.StepForQPc

@[expose] public section

/-! # No undefined behaviour in a lane, from a strict window under an invariant

`Frame.noUb_strict_lane` (`Lemmas/Kernel/NoUbStrictLane.lean`) for a machine whose strict steps
need an invariant `Q` of the concrete state and a well-formedness `Wf` of the events (a typed
register file, the words that loads returned): `Code.StepForQ`. The lane's machine follows the run
tolerantly to the state `dk0` before event `k0`, where `Q` holds by the state alone; from there
every step up to the event at hand is strict (`Code.strictQ_windowPc`), so the state before the
event is strictly good and satisfies `Q`, and the template of its site is not undefined behaviour
(`safe`). A machine that lost the lane before the event at hand lost it at an event that is the
exit (`live`). -/

namespace PTX.Frame

open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : ∀ g, Code K A L g} {J : ∀ g, (C g).D → Prop} {X : Execution}

/-- The machine's state after a window of events. -/
theorem stateAt_window {g k0 n : Nat} {dk0 dn : (C g).D}
    (h0 : stateAt C X g k0 = some (some dk0)) (h : stateAt C X g (k0 + n) = some (some dn)) :
    (C g).toMachine.after (some dk0) (((X.tr g).drop k0).take n) = some (some dn) := by
  unfold stateAt at h0 h
  rw [List.take_add] at h
  erw [Machine.after_append, h0] at h
  exact h

/-- **A lane has no undefined-behaviour event at the end of a strict window.** -/
theorem noUb_strictQ_lane (hC : ∀ g < L.threads, (C g).SoundU)
    (hX : Consistent L K A mem0 X) {g : Nat} (hF : ∀ k, FollowedAt C J X g k)
    {Q : TState → Prop} {Wf : Event → Prop} {Ok : (C g).D → Prop}
    (hS : ∀ d e, Ok d → (C g).StepForQ Q Wf d e)
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
    refine Code.strictQ_windowPc (hC g hg) hS hOk hr (Code.reach_init (hC g hg)) (by
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
