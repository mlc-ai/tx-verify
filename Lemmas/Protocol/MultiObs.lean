-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ObservedSync
public import Lemmas.Protocol.UnitNotify

@[expose] public section

/-! # Phase attribution without the reuse paths

A proof tool for a joint induction over dependency paths (`DepStep`), where the reuse paths of
one object (`Multi.Units.reach`) need the attribution of the phases of other objects, whose own
reuse paths need this one's. `Multi.Obs` is `Multi.Units` without `reach`: the history facts of
one object as its consumer's polls see it; `Obs.toUnits` adds the paths once they are proved.

* **A poll's content from the paths of what the polls up to it observe** (`Obs.content_le`): the
  consumer's poll for use `J` observes, for each kind, its unit of use `J`, when every unit that a
  poll for a use `j ≤ J` observes and whose use is above `j` follows that poll in the dependency
  order. In an induction along the dependency order towards a node `n` that the polls up to `J`
  precede, each such unit precedes `n` (it is a witness of one of them), so the induction
  hypothesis supplies its path (`Obs.content_of_reach`).
* **Earlier polls precede what a later one precedes** (`Poll.enables_earlier`), when polls are
  those of canonical spins.
* **A unit object or a commit object read by one consumer thread** (`Unit.Obj.obs`,
  `Notify.Obj.obs`): the history facts of `Unit.Obj.units` and `Notify.Obj.units`, without the
  paths. -/

namespace PTX.MbarRing

open Flow

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

namespace Multi

/-- One object whose phases each need one unit of every kind `κ`, as its consumer's polls see
it: `Units` without the reuse paths. -/
structure Obs (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (κ : Type)
    [Fintype κ] [DecidableEq κ] where
  /-- The counted units: those the object's history records. -/
  S : Finset (κ × Nat)
  /-- The phase a counted unit completes. -/
  ph : κ × Nat → Nat
  use : κ → Nat → Nat
  it : κ → Nat → AsyncCopy.Ref
  /-- The consumer's poll for use `j`. -/
  w : Nat → EvId
  /-- The completed phase the poll for use `j` observes. -/
  o : Nat → Nat
  /-- Distinct counted units of a kind have distinct uses. -/
  use_inj : ∀ k t t', (k, t) ∈ S → (k, t') ∈ S → use k t = use k t' → t = t'
  /-- The poll observes every counted unit of the phase it observes: the unit is a witness of
  the poll's return (DEP-ORDER). -/
  obs : ∀ j, X.RefPresent (.thread (w j)) → ∀ x ∈ S, ph x = o j →
    Witness L X (it x.1 x.2) (w j)
  /-- An observed phase holds at least one unit of each kind. -/
  full : ∀ j, X.RefPresent (.thread (w j)) →
    Fintype.card κ ≤ (S.filter (fun x => ph x = o j)).card
  /-- An earlier poll is present and observed an earlier phase. -/
  lt : ∀ j j', j < j' → X.RefPresent (.thread (w j')) →
    X.RefPresent (.thread (w j)) ∧ o j < o j'

namespace Obs
variable {κ : Type} [Fintype κ] [DecidableEq κ] (U : Obs L K A X κ)

/-- The units, once the reuse paths are proved. -/
def toUnits (hR : ∀ x ∈ U.S, ∀ j < U.use x.1 x.2,
    Relation.TransGen (DepStep L K X) (.thread (U.w j), true) (U.it x.1 x.2, false)) :
    Units L K A X κ where
  S := U.S
  ph := U.ph
  use := U.use
  it := U.it
  w := U.w
  o := U.o
  use_inj := U.use_inj
  obs := U.obs
  full := U.full
  lt := U.lt
  reach := hR

theorem present_le {j J : Nat} (hj : j ≤ J) (hw : X.RefPresent (.thread (U.w J))) :
    X.RefPresent (.thread (U.w j)) := by
  rcases Nat.lt_or_eq_of_le hj with h | rfl
  · exact (U.lt j J h hw).1
  · exact hw

/-- **The poll for use `J` observes, for each kind, its unit of use `J`**, given the paths of the
units observed by the polls up to `J`. -/
theorem content_le (hacyc : DepStepAcyclic L K X) {J : Nat}
    (hw : X.RefPresent (.thread (U.w J)))
    (hloc : ∀ j ≤ J, ∀ x ∈ U.S, U.ph x = U.o j → j < U.use x.1 x.2 →
      Relation.TransGen (DepStep L K X) (.thread (U.w j), true) (U.it x.1 x.2, false))
    (k : κ) :
    ∃ t, (k, t) ∈ U.S ∧ U.use k t = J ∧ Witness L X (U.it k t) (U.w J) := by
  have h := phase_of_counts U.S U.use U.use_inj U.ph U.o J
    (fun a b hab hb => (U.lt a b hab (U.present_le hb hw)).2)
    (fun a ha => U.full a (U.present_le ha hw))
    (fun a ha x hx hph => by
      by_contra hgt
      exact hacyc _ ((hloc a ha x hx hph (by omega)).tail
        (DepStep.of_witness L (U.obs a (U.present_le ha hw) x hx hph)))) J le_rfl
  obtain ⟨t, hS, hu, hp⟩ := h.2 k
  exact ⟨t, hS, hu, U.obs J hw (k, t) hS hp⟩

/-- **The content of a poll inside an induction along the dependency order**: when the polls up to
`J` precede `n`, the paths of the units that precede `n` give the content of the poll for use
`J`. -/
theorem content_of_reach (hacyc : DepStepAcyclic L K X) {J : Nat}
    {n : AsyncCopy.Ref × Bool} (hw : X.RefPresent (.thread (U.w J)))
    (hpath : ∀ j ≤ J, Relation.TransGen (DepStep L K X) (.thread (U.w j), true) n)
    (hih : ∀ x ∈ U.S, Relation.TransGen (DepStep L K X) (U.it x.1 x.2, false) n →
      ∀ j < U.use x.1 x.2,
        Relation.TransGen (DepStep L K X) (.thread (U.w j), true) (U.it x.1 x.2, false))
    (k : κ) :
    ∃ t, (k, t) ∈ U.S ∧ U.use k t = J ∧ Witness L X (U.it k t) (U.w J) :=
  U.content_le hacyc hw (fun j hj x hx hph hlt => hih x hx
    ((Relation.TransGen.single
      (DepStep.of_witness L (U.obs j (U.present_le hj hw) x hx hph))).trans (hpath j hj)) j hlt) k

end Obs
end Multi

/-- **Earlier polls precede what a later one precedes**: the poll with `j ≤ J` earlier successful
polls of `m` resumes into the poll with `J`, when polls are those of canonical spins. -/
theorem Poll.enables_earlier
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {g J j : Nat} {m : Loc} {n : AsyncCopy.Ref × Bool} (hj : j ≤ J)
    (hJ : J < okPolls m (X.tr g))
    (h : Relation.TransGen (DepStep L K X) (.thread (g, Poll.nth X m g J), true) n) :
    Relation.TransGen (DepStep L K X) (.thread (g, Poll.nth X m g j), true) n := by
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · obtain ⟨pc, p, acq, sc, he, hc⟩ := Poll.nth_spec hJ
    have hg := Poll.guard hspin (k := Poll.nth X m g J) (len_of_get he) (n := j) (m := m)
      (g := g) (by omega)
    exact .head (DepStep.of_resumes L hg) (.head (DepStep.node ⟨_, he⟩) h)
  · exact h

namespace Unit

variable {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- **A unit object read by one consumer thread**, without the reuse paths. -/
def Obj.obs (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) (g : Nat) :
    Multi.Obs L K A X (Fin N) where
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

end Unit

namespace Notify

variable {m m0 : Loc} {g δ : Nat}

/-- **A commit object read by one consumer thread**, without the reuse paths. -/
def Obj.obs (hX : Consistent L K A mem0 X) (O : Obj X m g m0 δ) (h : Nat) :
    Multi.Obs L K A X (Fin 1) where
  S := S X m g m0
  ph := ph X m g m0
  use _ t := t
  it _ t := it X m g m0 t
  w j := (h, Poll.nth X m h (j + δ))
  o j := Unit.obsOf X m h (j + δ)
  use_inj _ _ _ _ _ he := he
  obs _ hp _ hx hph := O.observed hX (Nat.le_add_left _ _) (Poll.nth_present.mp hp) hx hph
  full _ hp := by
    classical
    convert O.card_phase hX (Nat.le_add_left _ _) (Poll.nth_present.mp hp) using 1
    simp
  lt _ _ hjj hp := ⟨Poll.nth_present.mpr (by have := Poll.nth_present.mp hp; omega),
    Poll.observed_lt hX O.δ_le (O.pclean hX) O.noInval (O.alt hX h) (Nat.le_add_left _ _)
      (by omega) (Poll.nth_present.mp hp)⟩

end Notify

end
end PTX.MbarRing
