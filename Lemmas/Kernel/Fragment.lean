-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed
public import Lemmas.Kernel.FrameStop
public import Lemmas.Flow.Fragment

@[expose] public section

/-! # Fragments in an execution: followed, no undefined behaviour

A proof skeleton, generic over the kernel. Each thread `g` is followed by the machine of a
fragment `F g` (`Flow.Fragment`) whose obligations hold (`Fragment.Ok`). Write `codes F` for the
machines and `refs F` for the reference invariants.

* For one thread (`thread_followed`, `thread_noUb`): when every event among its first `n` that is
  fired from a state satisfying `Ref` returns what `Expect` says, the thread is followed with
  `Ref` up to its `n`-th event, none of its first `n` events is undefined behaviour, and its
  machine is dead before event `n` only after an exit.
* For the execution (`followed_of_sources`, `noUb_of_sources`): with an order that has an
  induction principle (`Frame.Inductive`), it suffices that each event fired from a state
  satisfying `Ref`, none of whose predecessors in the order is bad, returns what `Expect` says
  (the source obligation, met by the lemmas of `Lemmas/Kernel/Source/`). Then every launched
  thread is followed with `Ref` at every state, and no event is undefined behaviour. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- The machines of a kernel's fragments. -/
abbrev codes (F : (g : Nat) → Fragment K A L g) : (g : Nat) → Code K A L g := fun g => (F g).code

/-- The reference invariants of a kernel's fragments. -/
abbrev refs (F : (g : Nat) → Fragment K A L g) : ∀ g, (codes F g).D → Prop := fun g => (F g).Ref

variable {F : (g : Nat) → Fragment K A L g} {X : Execution} {g : Nat}

/-- An expected event at a state satisfying `Ref` makes a good step. -/
theorem stepGood_of {d : (F g).code.D} {e : Event} (hok : (F g).OkAt d) (hi : (F g).code.inv d)
    (hJ : (F g).Ref d) (hE : (F g).Expect d e) (hev : (F g).Ev d e) :
    StepGood (codes F) (refs F) g d e :=
  ⟨(hok.ref_next hi hJ hE hev).1, (hok.ref_next hi hJ hE hev).2.2⟩

variable (hC : ∀ g < L.threads, (F g).code.Sound) (hok : ∀ g < L.threads, (F g).Ok)
  (hX : Consistent L K A mem0 X)
include hC hok hX

/-- An event fired from a followed state has the state's shape, and the state its invariant. -/
theorem fired_ev {k : Nat} {d : (F g).code.D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : stateAt (codes F) X g k = some (some d)) : (F g).Ev d e ∧ (F g).code.inv d := by
  have hg := lt_of_get hX he
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := fired_site (C := codes F) hC hX he hσ
  exact ⟨(hok g hg d).shape hat hi hc hf, hi⟩

/-- **A thread whose first `n` events at `Ref` states are expected is followed with `Ref` up to
its `n`-th event.** -/
theorem thread_followed (h0 : (F g).Ref (F g).code.init) {n : Nat}
    (hE : ∀ j < n, ∀ d e, X.get (g, j) = some e → stateAt (codes F) X g j = some (some d) →
      (F g).Ref d → (F g).Expect d e) :
    ∀ k ≤ n, FollowedAt (codes F) (refs F) X g k := by
  intro k hk
  refine followedAt_of_noBad (C := codes F) (J := refs F) h0 k fun j hj hB => ?_
  obtain ⟨d, e, he, hσ, hJ, hbad⟩ := hB
  have hg := lt_of_get hX he
  obtain ⟨hev, hi⟩ := fired_ev hC hok hX he hσ
  exact hbad (stepGood_of (hok g hg d) hi hJ (hE j (by omega) d e he hσ hJ) hev)

/-- **No undefined behaviour among the first `n` events of such a thread, and its machine is
dead before event `n` only after an exit.** -/
theorem thread_noUb (h0 : (F g).Ref (F g).code.init) {n : Nat}
    (hE : ∀ j < n, ∀ d e, X.get (g, j) = some e → stateAt (codes F) X g j = some (some d) →
      (F g).Ref d → (F g).Expect d e) :
    (∀ j < n, ∀ e, X.get (g, j) = some e → ∀ f, e.kind ≠ .ub f) ∧
      ∀ k ≤ n, stateAt (codes F) X g k = none →
        ∃ j < k, ∃ pc, X.get (g, j) = some ⟨pc, .exit⟩ := by
  have hfol := thread_followed hC hok hX h0 hE
  -- a dead machine died at an exit
  have hdead : ∀ k ≤ n, stateAt (codes F) X g k = none →
      ∃ j < k, ∃ pc, X.get (g, j) = some ⟨pc, .exit⟩ := by
    intro k hk hσ
    obtain ⟨i, d, hik, hi, hi'⟩ := first_stop_any (C := codes F) (X := X) (g := g) (.inl hσ)
    have hlen : i < (X.tr g).length := by
      by_contra hn
      rw [stateAt_of_le (by omega)] at hi
      rw [stateAt_of_le (by omega), hi] at hi'
      simp at hi'
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
    have hJ := (hfol i (by omega)).2 d hi
    have hg := lt_of_get hX he
    obtain ⟨hev, hinv⟩ := fired_ev hC hok hX he hi
    have hr := (hok g hg d).ref_next hinv hJ (hE i (by omega) d e he hi hJ) hev
    rw [stateAt_succ he, hi] at hi'
    rcases hi' with hn | hn
    · rcases hr.2.1 hn with ⟨f, hf⟩ | hx
      · exact absurd hf ((hok g hg d).ref_safe hinv hJ hev f)
      · obtain ⟨pc, kd⟩ := e
        exact ⟨i, hik, pc, by rw [he, show kd = .exit from hx]⟩
    · exact absurd hn hr.1
  refine ⟨fun j hj e he f hf => ?_, hdead⟩
  have hg := lt_of_get hX he
  rcases fired (C := codes F) hC hX he with ⟨σ, o, hσ, -⟩ | ⟨hσ, -⟩
  · cases σ with
    | none => exact (hfol j (by omega)).1 hσ
    | some d =>
      obtain ⟨hev, hinv⟩ := fired_ev hC hok hX he hσ
      exact (hok g hg d).ref_safe hinv ((hfol j (by omega)).2 d hσ) hev f hf
  · obtain ⟨i, hij, pc, hx⟩ := hdead j (by omega) hσ
    obtain ⟨r, hr⟩ := hX.thr g hg
    have h1 := Flow.Run.end_last hr hx (.inr rfl)
    have h2 : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    omega

omit hC hok hX in
/-- After no event is bad, the source obligation gives every event at a `Ref` state its expected
value. -/
theorem expect_of_noBad {r : EvId → EvId → Prop}
    (src : ∀ g k d e, X.get (g, k) = some e → stateAt (codes F) X g k = some (some d) →
      (F g).code.inv d → (F g).Ref d → (F g).Ev d e →
      (∀ j, r j (g, k) → ¬ Bad (codes F) (refs F) X j) → (F g).Expect d e)
    (hnb : ∀ i, ¬ Bad (codes F) (refs F) X i) (hev : ∀ g k d e, X.get (g, k) = some e →
      stateAt (codes F) X g k = some (some d) → (F g).Ev d e ∧ (F g).code.inv d)
    {g j : Nat} {d : (F g).code.D} {e : Event} (he : X.get (g, j) = some e)
    (hσ : stateAt (codes F) X g j = some (some d)) (hJ : (F g).Ref d) : (F g).Expect d e :=
  src g j d e he hσ (hev g j d e he hσ).2 hJ (hev g j d e he hσ).1 fun i _ => hnb i

/-- No event is bad, given the source obligation along an order with an induction principle. -/
theorem noBad_of_sources {r : EvId → EvId → Prop} (hr : Inductive X r)
    (src : ∀ g k d e, X.get (g, k) = some e → stateAt (codes F) X g k = some (some d) →
      (F g).code.inv d → (F g).Ref d → (F g).Ev d e →
      (∀ j, r j (g, k) → ¬ Bad (codes F) (refs F) X j) → (F g).Expect d e) :
    ∀ i, ¬ Bad (codes F) (refs F) X i :=
  noBad hr fun g k d e he hσ hJ hprev => by
    have hg := lt_of_get hX he
    obtain ⟨hev, hi⟩ := fired_ev hC hok hX he hσ
    exact stepGood_of (hok g hg d) hi hJ (src g k d e he hσ hi hJ hev hprev) hev

/-- **Every launched thread is followed, with `Ref` at every state**, given the source
obligation along an order with an induction principle. -/
theorem followed_of_sources {r : EvId → EvId → Prop} (hr : Inductive X r)
    (h0 : ∀ g < L.threads, (F g).Ref (F g).code.init)
    (src : ∀ g k d e, X.get (g, k) = some e → stateAt (codes F) X g k = some (some d) →
      (F g).code.inv d → (F g).Ref d → (F g).Ev d e →
      (∀ j, r j (g, k) → ¬ Bad (codes F) (refs F) X j) → (F g).Expect d e) :
    ∀ g < L.threads, ∀ k, FollowedAt (codes F) (refs F) X g k := by
  have hnb := noBad_of_sources hC hok hX hr src
  exact fun g hg k => followedAt_of_noBad (h0 g hg) k fun j _ => hnb (g, j)

/-- **No event is undefined behaviour, and a machine is dead only after an exit**, given the
source obligation along an order with an induction principle. -/
theorem noUb_of_sources {r : EvId → EvId → Prop} (hr : Inductive X r)
    (h0 : ∀ g < L.threads, (F g).Ref (F g).code.init)
    (src : ∀ g k d e, X.get (g, k) = some e → stateAt (codes F) X g k = some (some d) →
      (F g).code.inv d → (F g).Ref d → (F g).Ev d e →
      (∀ j, r j (g, k) → ¬ Bad (codes F) (refs F) X j) → (F g).Expect d e) :
    ¬ HasUb X ∧ ∀ g < L.threads, ∀ k, stateAt (codes F) X g k = none →
      ∃ j < k, ∃ pc, X.get (g, j) = some ⟨pc, .exit⟩ := by
  have hnb := noBad_of_sources hC hok hX hr src
  have hE : ∀ g j d e, X.get (g, j) = some e → stateAt (codes F) X g j = some (some d) →
      (F g).Ref d → (F g).Expect d e := fun g j d e he hσ hJ =>
    expect_of_noBad src hnb (fun g k d e he hσ => fired_ev hC hok hX he hσ) he hσ hJ
  refine ⟨fun ⟨⟨g, j⟩, pc, f, he⟩ => ?_, fun g hg k hσ => ?_⟩
  · have hg := lt_of_get hX he
    exact (thread_noUb (n := j + 1) hC hok hX (h0 g hg) fun j _ d e => hE g j d e).1 j
      (by omega) _ he f rfl
  · exact (thread_noUb (n := k) hC hok hX (h0 g hg) fun j _ d e => hE g j d e).2 k le_rfl hσ

end

end PTX.Frame
