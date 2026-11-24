-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine

@[expose] public section

/-! # Work bounds from a rank on abstract states

A proof tool. If no machine step increases a natural-number rank and every counted event
(anything but a failed `try_wait`) decreases it, a run from `σ` has at most `rank σ + 1`
counted events: the `+ 2` is an event into a dead state and its undefined behaviour. -/

namespace PTX.Flow.Machine

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {M : Machine K A L g}

theorem Trace.count_le (rank : M.St → Nat)
    (hdec : ∀ σ σ' e, M.next σ e = some σ' → rank σ' + (if e.counts then 1 else 0) ≤ rank σ)
    {σ : M.St} {es : List Event} (h : M.Trace σ es) :
    es.countP Event.counts ≤ rank σ + 2 := by
  induction h with
  | nil => simp
  | @step σ σ' e es u _ hn _ ih =>
    have hd := hdec σ σ' e hn
    rw [List.countP_cons]
    split_ifs at hd ⊢ <;> omega
  | last => exact List.countP_le_length.trans (by simp)
  | dead _ _ hlen =>
    exact List.countP_le_length.trans (by simp only [List.length_cons]; omega)

/-- The counted events of a produced trace, bounded by the rank of the initial state. -/
theorem Sound.count_le (hM : M.Sound) (rank : M.St → Nat)
    (hdec : ∀ σ σ' e, M.next σ e = some σ' → rank σ' + (if e.counts then 1 else 0) ≤ rank σ)
    {es : List Event} (hp : Produces K A L g es) :
    es.countP Event.counts ≤ rank M.init + 2 :=
  (hM.produces hp).count_le rank hdec

/-- Work bounds with resets, at the trace's positions: the step
at position `k` may use the states before and after the `k`-th event. -/
theorem Trace.count_le_resets_at (rank : M.St → Nat) (reset : Event → Bool) (C : Nat)
    {σ : M.St} {es : List Event} (h : M.Trace σ es)
    (hdec : ∀ k e σ1 σ2 u, es[k]? = some e → M.after σ (es.take k) = some σ1 →
      M.after σ (es.take (k + 1)) = some σ2 → M.Fired σ1 e (some u) →
      rank σ2 + (if e.counts then 1 else 0) ≤ rank σ1 + (if reset e then C else 0)) :
    es.countP Event.counts ≤ rank σ + 2 + C * es.countP reset := by
  induction h with
  | nil => simp
  | @step σ σ' e es u hfire hn _ ih =>
    have hd := hdec 0 e σ σ' u (by simp) (by simp) (by simp [hn]) hfire
    have ih' := ih fun k e' σ1 σ2 u' hk h1 h2 hf =>
      hdec (k + 1) e' σ1 σ2 u' (by simpa using hk) (by simpa [hn] using h1)
        (by simpa [hn] using h2) hf
    rw [List.countP_cons, List.countP_cons, Nat.mul_add]
    split_ifs at hd ⊢ <;> omega
  | last => exact List.countP_le_length.trans (by simp only [List.length_singleton]; omega)
  | dead _ _ hlen =>
    exact List.countP_le_length.trans (by simp only [List.length_cons]; omega)

end PTX.Flow.Machine

namespace PTX.Flow

end PTX.Flow
