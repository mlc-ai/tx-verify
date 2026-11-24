-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitItems
public import Lemmas.Protocol.MultiProducer

@[expose] public section

/-! # From an observed arrival to a synchronization

A proof tool bridging the attribution of an object's phases (`MbarRing.Multi.Units`, whose
consumer polls have the units of their phase as `Witness`es) to the memory synchronization form
the protocols use (`AsyncCopy.WaitObserves`, `MbarRing.Syncs`, `MbarRing.UnitHandoff`).

* The source of a dependency step from a thread event's return is present
  (`DepStep.present_of_return`).
* A witness of a successful poll is a counter update it observed (`Witness.mbarObserved`, from
  `pollNeeds`), so it is the object's observation (`Witness.waitObserves`; for a commit's
  notification, which then occurred, `Witness.waitObserves_tcNotify`); with a release arrival, an
  acquire poll and scopes that meet it is a synchronization (`Witness.syncs`).
* **Units of thread arrivals give the unit handoff** (`UnitHandoff.of_units`): when each consumer
  thread's polls are read as `Units` whose unit `(a, t)` is producer `a`'s arrival with `t`
  earlier ones, a consumer's poll with `q + δ` earlier successful polls synchronizes with every
  producer's arrival of use `q`.
* **A unit object read by one consumer thread** (`Unit.Obj.units`, `Unit.Obj.handoff`): the units
  of a unit object (`UnitItems`) polled by one thread, given the dependency paths of its reuse
  (`Unit.Reach`), and the unit handoff they give. -/

namespace PTX
open Flow
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **The source of a dependency step from the return of a thread event is present**: the only
step out of a thread event's return is to an event that resumes from it. -/
theorem DepStep.present_of_return {w : EvId} {c : AsyncCopy.Ref × Bool}
    (h : DepStep L K X (.thread w, true) c) : X.RefPresent (.thread w) := by
  obtain ⟨f, b'⟩ := c
  rcases h with (⟨-, h, -⟩ | ⟨-, -, hs⟩) | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, w', j, hw, -, ⟨h1, h2, h3⟩, -⟩
  · cases h
  · cases f <;> cases hs
  · cases h
  · cases h
  · cases hw
    exact present_of_len (by rw [h1]; omega)

/-- **A witness of a successful poll is the object's observation.** -/
theorem Witness.waitObserves {x : AsyncCopy.Ref} {w : EvId} (ho : Witness L X x w) {pc p : Nat}
    {m : Loc} {acq : Bool} {sc : MbarScope} (hw : X.get w = some ⟨pc, .wait m p true acq sc⟩) :
    X.RefPresent x ∧ AsyncCopy.WaitObserves X x w m acq sc := by
  obtain ⟨hpres, j, m', acq', ws, hj, ⟨⟨pc', p', hw'⟩, hu⟩, -⟩ := ho.mbarObserved hw
  cases hj
  rw [hw] at hw'
  cases hw'
  exact ⟨hpres, ⟨pc, p, hw⟩, hu⟩

/-- **A witness of a successful poll that is a commit's notification is the object's
observation**, and the notification occurred. -/
theorem Witness.waitObserves_tcNotify {x w : EvId} {rank : Fin 16}
    (ho : Witness L X (.async x (.tcNotify rank)) w) {pc p : Nat} {m : Loc}
    {acq : Bool} {sc : MbarScope} (hw : X.get w = some ⟨pc, .wait m p true acq sc⟩) :
    rank ∈ X.tcNotified x ∧ AsyncCopy.WaitObserves X (.async x (.tcNotify rank)) w m acq sc :=
  ho.waitObserves hw

/-- **A witnessed release arrival synchronizes with an acquire poll** whose scope meets it. -/
theorem Witness.syncs {x w : EvId} (ho : Witness L X (.thread x) w) {pc p : Nat} {m : Loc}
    {rs sc : MbarScope} (hx : MbarRelease X x m rs)
    (hw : X.get w = some ⟨pc, .wait m p true true sc⟩) (hsc : ScopesMeet L rs x.1 sc w.1) :
    MbarRing.Syncs L X x w m :=
  ⟨rs, hx, sc, (ho.waitObserves hw).2, hsc⟩

namespace MbarRing

/-- **Units of thread arrivals give the unit handoff.** Consumer `h`'s polls are read as units
`U h` whose poll for use `j` is its successful poll of `m` with `j + δ` earlier ones and whose
unit `(a, t)` is producer `a`'s arrival on `m` with `t` earlier ones. When the counted units are
release arrivals whose scopes meet the acquire polls (`hsync`), the handoff of `m` holds with
offset `δ`. -/
theorem UnitHandoff.of_units (hX : Consistent L K A mem0 X) {m : Loc} {N δ : Nat}
    {prod : Fin N → Nat} {cons : Nat → Prop} (U : ∀ h, cons h → Multi.Units L K A X (Fin N))
    (hw : ∀ h hh j, (U h hh).w j = (h, Poll.nth X m h (j + δ)))
    (hit : ∀ h hh a t, (U h hh).it a t = .thread (prod a, nthEv X (Flow.arrivesOn m) (prod a) t))
    (huse : ∀ h hh a t, (U h hh).use a t = t)
    (hacq : ∀ {h j pc p : Nat} {acq : Bool} {sc : MbarScope}, cons h →
      X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩ → acq = true)
    (hsync : ∀ h hh, ∀ x ∈ (U h hh).S, ∀ {j pc p : Nat} {sc : MbarScope},
      X.get (h, j) = some ⟨pc, .wait m p true true sc⟩ →
      ∃ rs, MbarRelease X (prod x.1, nthEv X (Flow.arrivesOn m) (prod x.1) x.2) m rs ∧
        ScopesMeet L rs (prod x.1) sc h) :
    UnitHandoff L X m (fun g => ∃ a, g = prod a) cons δ := by
  intro h j pc p acq sc q hh he hq g ⟨a, hga⟩
  subst hga
  have hacq' := hacq hh he
  subst hacq'
  have hjn : Poll.nth X m h (q + δ) = j := by
    rw [← hq]
    exact Poll.nth_eq he
  have hpw : X.RefPresent (.thread ((U h hh).w q)) := by
    rw [hw, hjn]
    exact ⟨_, he⟩
  obtain ⟨t, hS, ht, hobs⟩ := (U h hh).observes hX.depAcyclic hpw a
  rw [huse] at ht
  subst ht
  rw [hit, hw, hjn] at hobs
  obtain ⟨⟨ev, hev⟩, hwo⟩ := hobs.waitObserves he
  obtain ⟨rs, hrel, hs⟩ := hsync h hh _ hS he
  exact ⟨_, (nthEv_spec_of_get hev).2, rs, hrel, sc, hwo, hs⟩

end MbarRing

namespace MbarRing.Unit

open AsyncCopy Flow

variable {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- **The reuse of a unit object as thread `g` polls it**: producer `a`'s arrival of use `t`
follows, in the dependency order, `g`'s polls for the uses before `t` (its successful polls with
`j + δ` earlier ones, `j < t`). -/
def Reach (L : Launch) (K : Kernel) (_A : List Assumption) (X : Execution) (m : Loc) (N : Nat)
    (prod : Fin N → Nat) (δ g : Nat) : Prop :=
  ∀ x ∈ S X m prod, ∀ j < x.2,
    Relation.TransGen (DepStep L K X) (.thread (g, Poll.nth X m g (j + δ)), true)
      (.thread (it X m prod x.1 x.2), false)

/-- **A unit object read by one consumer thread.** -/
def Obj.units (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) (g : Nat)
    (hR : Reach L K A X m N prod δ g) : Multi.Units L K A X (Fin N) where
  S := S X m prod
  ph := ph X m prod
  use _ t := t
  it a t := .thread (it X m prod a t)
  w j := (g, Poll.nth X m g (j + δ))
  o j := obsOf X m g (j + δ)
  use_inj _ _ _ _ _ h := h
  obs _ hp _ hx hph := O.observed hX (Nat.le_add_left _ _) (Poll.nth_present.mp hp) hx hph
  full _ hp := by
    classical
    convert O.card_phase hX (Nat.le_add_left _ _) (Poll.nth_present.mp hp) using 1
    simp
  lt _ _ hjj hp := ⟨Poll.nth_present.mpr (by have := Poll.nth_present.mp hp; omega),
    Poll.observed_lt hX O.δ_le (O.pclean hX) O.noInval (O.alt hX g) (Nat.le_add_left _ _)
      (by omega) (Poll.nth_present.mp hp)⟩
  reach x hx j hj := hR x hx j hj

/-- **The unit handoff of a unit object** whose every consumer thread's reuse precedes the
producers' arrivals (`Reach`), with acquire polls and scopes that meet. -/
theorem Obj.handoff (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {cons : Nat → Prop}
    (hR : ∀ h, cons h → Reach L K A X m N prod δ h)
    (hacq : ∀ {h j pc p : Nat} {acq : Bool} {sc : MbarScope}, cons h →
      X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩ → acq = true)
    (hsc : ∀ {a : Fin N} {h i j pc pc' p : Nat} {acq : Bool} {sc sc' : MbarScope},
      cons h → X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ →
      X.get (h, j) = some ⟨pc', .wait m p true acq sc'⟩ → ScopesMeet L sc (prod a) sc' h) :
    UnitHandoff L X m (fun g => ∃ a, g = prod a) cons δ := by
  refine UnitHandoff.of_units hX (fun h hh => O.units hX h (hR h hh)) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hacq (fun h hh x hx _ _ _ _ hw => ?_)
  obtain ⟨-, ⟨pca, sca, hea⟩, -⟩ := O.S_rec hx
  exact ⟨sca, ⟨0, 1, pca, hea⟩, hsc hh hea hw⟩

end MbarRing.Unit

end
end PTX
