-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Handoff
public import Lemmas.Kernel.Safety.Classes
public import Core.MBarrier.InitPublication

@[expose] public section

/-! # mbarrier initialization from a role table

A proof skeleton, generic over the kernel, for ERR-MBAR-UNINITIALIZED (`MbarUninit`): every event
that names an mbarrier operand and is not its initialization has an initialization of the object
published to it.

* `RoleTable.noMbarUninit`: per state. An event of a thread of `S` that names an object
  (`MbarOf`) and is no initialization of it is fired from a followed state with its shape; the
  kernel states, per shape, an initialization published to the event (`InitPublished`). Events of
  other threads are the kernel's (`hout`).
* `RoleTable.noMbarUninit_of_handoff`: the publication by a declared hand-off (the startup's CTA
  barrier, `Frame.Handoff.of_bar`). The kernel names the initialization of each object of a
  thread's object frame (`ini g m`, an event of a thread that hands off to `g`), and states per
  state that the use is after the hand-off: the initialization's producer use is below the use's
  consumer use (in practice: the initializing thread's barrier count at the initialization is `0`
  and the user's barrier count before the use is positive, both ledger counts). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

/-- An mbarrier use that names an object at its event and is no initialization of it. -/
theorem usesMbar_not_init {i : EvId} {m : Loc} {e : Event} (he : X.get i = some e)
    (hni : ∀ count, ¬ X.MbInit i m count) : ∀ c, e.kind ≠ .mbInit m c := by
  intro c hk
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  exact hni c ⟨pc, he⟩

variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S)
  (hF : T.Followed X S)
include hC hX hT hF

/-- **ERR-MBAR-UNINITIALIZED from a role table**: every use of an object by a thread of `S` that
is no initialization of it has, per its issuing state, a published initialization; uses by other
threads are the kernel's. -/
theorem RoleTable.noMbarUninit
    (hpub : ∀ g k d e m, S g → stateAt C X g k = some (some d) → T.J g d → (C g).inv d →
      T.Ev g d e → X.get (g, k) = some e → MbarOf e m → (∀ c, e.kind ≠ .mbInit m c) →
      ∃ i count, X.MbInit i m count ∧ InitPublished L X i (g, k) m)
    (hout : ∀ i m, X.UsesMbar i m → ¬ S i.1 → (∀ count, ¬ X.MbInit i m count) →
      ∃ j count, X.MbInit j m count ∧ InitPublished L X j i m) :
    ¬ MbarUninit L X := by
  rintro ⟨⟨g, k⟩, m, hu, hni, hno⟩
  by_cases hg : S g
  · obtain ⟨e, he, hm⟩ := usesMbar_mbarOf hu
    have hub : ∀ f, e.kind ≠ .ub f := by
      obtain ⟨pc, kd⟩ := e
      rintro f rfl
      simp only [MbarOf] at hm
    obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hg he hub
    exact hno (hpub g k d e m hg hσ hJ hi hev he hm (usesMbar_not_init he hni))
  · exact hno (hout _ m hu hg hni)

/-- **ERR-MBAR-UNINITIALIZED from a hand-off**: the initialization `ini g m` of every object `m`
of a thread's object frame `O g` is an initialization of `m` by a thread that hands off to `g`
(`hini`), and every use is, per its issuing state, after the hand-off (`hord`). -/
theorem RoleTable.noMbarUninit_of_handoff {pair : Nat → Nat → Prop} {up uq : EvId → Nat}
    (H : Handoff L X pair up uq) {O : Nat → Loc → Prop}
    (hO : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ m, MbarOf e m → O g m)
    (ini : Nat → Loc → EvId)
    (hini : ∀ g m, S g → O g m → (∃ count, X.MbInit (ini g m) m count) ∧ pair (ini g m).1 g)
    (hord : ∀ g k d e m, S g → stateAt C X g k = some (some d) → T.J g d → (C g).inv d →
      T.Ev g d e → X.get (g, k) = some e → MbarOf e m → (∀ c, e.kind ≠ .mbInit m c) →
      up (ini g m) < uq (g, k))
    (hout : ∀ i m, X.UsesMbar i m → ¬ S i.1 → (∀ count, ¬ X.MbInit i m count) →
      ∃ j count, X.MbInit j m count ∧ InitPublished L X j i m) :
    ¬ MbarUninit L X := by
  refine RoleTable.noMbarUninit hC hX hT hF
    (fun g k d e m hg hσ hJ hi hev he hm hni => ?_) hout
  have hOm := hO g hg d e hJ hi hev m hm
  obtain ⟨⟨count, hinit⟩, hp⟩ := hini g m hg hOm
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  exact ⟨ini g m, count, hinit,
    .inl (H _ g _ k hp hk (hord g k d e m hg hσ hJ hi hev he hm hni))⟩

end

end PTX.Frame
