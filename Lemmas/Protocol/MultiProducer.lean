-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Order.DependencyWitness

@[expose] public section

/-! # Phases of an object completed by producers with their own counters

A proof tool for an mbarrier object whose every phase needs one unit of each of several kinds,
where the producer of a kind numbers its units by its own counter, which need not be the use
number (FA4's P-ready object: the softmax arrives once per tile, the correction once per credit,
and a phase holds tile `i`'s arrivals and credit `i`'s). Kind `k`'s unit number `t` is attributed
to use `use k t`; distinct units of a kind have distinct uses.

`phase_of_counts` is the counting argument on one object's history: when the observed phases
`o 0 < o 1 < … < o J` each hold at least one unit of every kind and the units of phase `o j` have
uses at most `j`, phase `o j` holds exactly the units of use `j`, one of each kind. It generalises
`MbarRing.Items.content` (where the unit number is the use) to per-kind counters.

`Units` reads this on an execution: the consumer's poll for use `j` observes a completed phase and
every unit of it, each a `Witness` of the poll's return (DEP-ORDER), and each unit of use `s`
depends on the consumer's polls for the uses before `s` (the kernel's reuse gate, possibly through
other protocols). Then the poll for use `j` observes exactly the units of use `j`
(`Units.content`), one of each kind (`Units.observes`). The witness is the edge that
`Units.content` closes into a cycle; `Witness.of_mbarObserved` and `SyncObserved.witness` give it
from an observation. -/

namespace PTX.MbarRing.Multi

/-- **Phase attribution with per-kind counters.** -/
theorem phase_of_counts {κ : Type} [Fintype κ] [DecidableEq κ] (S : Finset (κ × Nat))
    (use : κ → Nat → Nat) (huse : ∀ k t t', (k, t) ∈ S → (k, t') ∈ S → use k t = use k t' → t = t')
    (ph : κ × Nat → Nat) (o : Nat → Nat) (J : Nat)
    (hlt : ∀ j j', j < j' → j' ≤ J → o j < o j')
    (hfull : ∀ j ≤ J, Fintype.card κ ≤ (S.filter (fun x => ph x = o j)).card)
    (hle : ∀ j ≤ J, ∀ x ∈ S, ph x = o j → use x.1 x.2 ≤ j) :
    ∀ j ≤ J, (∀ x ∈ S, ph x = o j → use x.1 x.2 = j) ∧
      ∀ k, ∃ t, (k, t) ∈ S ∧ use k t = j ∧ ph (k, t) = o j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have h1 : ∀ x ∈ S, ph x = o j → use x.1 x.2 = j := by
      intro x hx hp
      have hle' := hle j hj x hx hp
      by_contra hne
      have hlt' : use x.1 x.2 < j := by omega
      obtain ⟨-, h2⟩ := ih _ hlt' (by omega)
      obtain ⟨t, ht, hut, hpt⟩ := h2 x.1
      have heq : t = x.2 := huse x.1 t x.2 ht (by simpa using hx) hut
      subst heq
      rw [Prod.mk.eta, hp] at hpt
      have := hlt _ j hlt' hj
      omega
    refine ⟨h1, fun k => ?_⟩
    set F := S.filter (fun x => ph x = o j)
    have hinj : Set.InjOn Prod.fst (F : Set (κ × Nat)) := by
      intro x hx y hy hxy
      obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyS, hyp⟩ := Finset.mem_filter.mp hy
      have hux := h1 x hxS hxp
      have huy := h1 y hyS hyp
      have hy' : (x.1, y.2) ∈ S := by rw [hxy]; simpa using hyS
      have huy' : use x.1 y.2 = j := by rw [hxy]; exact huy
      have h2 : x.2 = y.2 := huse x.1 x.2 y.2 (by simpa using hxS) hy' (hux.trans huy'.symm)
      exact Prod.ext hxy h2
    have hcard : (F.image Prod.fst).card = Fintype.card κ := by
      have hle' := Finset.card_le_univ (F.image Prod.fst)
      have hge : Fintype.card κ ≤ (F.image Prod.fst).card := by
        rw [Finset.card_image_of_injOn hinj]
        exact hfull j hj
      omega
    have hk : k ∈ F.image Prod.fst := by
      rw [Finset.eq_univ_of_card _ hcard]
      exact Finset.mem_univ k
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
    exact ⟨x.2, by simpa using hxS, h1 x hxS hxp, by simpa using hxp⟩

section
variable {L : Launch} {X : Execution}

/-- An observed counter update or covered stage fills a need of the observer's return. -/
theorem SyncObserved.witness {x : AsyncCopy.Ref} {w : EvId}
    (h : SyncObserved L X x (.thread w)) : Witness L X x w := by
  rcases h with ⟨ho, -⟩ | ⟨i, p, j, k, hev, hev', hpres, hw, hstage⟩
  · exact Witness.of_mbarObserved ho
  · cases hev
    cases hev'
    exact hw.witness hstage hpres

end

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- One object whose phases each need one unit of every kind `κ`, as its consumer's polls see
it. Kind `k`'s unit number `t` has the record `it k t` and is attributed to use `use k t`. -/
structure Units (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (κ : Type)
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
  /-- A counted unit of use `s` depends on the consumer's polls for the uses before `s`. -/
  reach : ∀ x ∈ S, ∀ j < use x.1 x.2,
    Relation.TransGen (DepStep L K X) (.thread (w j), true) (it x.1 x.2, false)

namespace Units
variable {κ : Type} [Fintype κ] [DecidableEq κ] (U : Units L K A X κ)

/-- **The consumer's poll for use `j` observes a phase holding exactly the units of use `j`**,
one of each kind. -/
theorem content (hacyc : DepStepAcyclic L K X) {j : Nat} (hw : X.RefPresent (.thread (U.w j))) :
    (∀ x ∈ U.S, U.ph x = U.o j → U.use x.1 x.2 = j) ∧
      ∀ k, ∃ t, (k, t) ∈ U.S ∧ U.use k t = j ∧ U.ph (k, t) = U.o j := by
  have hp : ∀ j' ≤ j, X.RefPresent (.thread (U.w j')) := fun j' hj => by
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · exact (U.lt j' j h hw).1
    · exact hw
  refine phase_of_counts U.S U.use U.use_inj U.ph U.o j
    (fun a b hab hb => (U.lt a b hab (hp b hb)).2) (fun a ha => U.full a (hp a ha))
    (fun a ha x hx hph => ?_) j le_rfl
  by_contra hgt
  exact hacyc _ ((U.reach x hx a (by omega)).tail
    (DepStep.of_witness L (U.obs a (hp a ha) x hx hph)))

/-- **The poll for use `j` observes, for each kind, its unit of use `j`.** -/
theorem observes (hacyc : DepStepAcyclic L K X) {j : Nat}
    (hw : X.RefPresent (.thread (U.w j))) (k : κ) :
    ∃ t, (k, t) ∈ U.S ∧ U.use k t = j ∧
      Witness L X (U.it k t) (U.w j) := by
  obtain ⟨t, hS, hu, hp⟩ := (U.content hacyc hw).2 k
  exact ⟨t, hS, hu, U.obs j hw (k, t) hS hp⟩

end Units
end
end PTX.MbarRing.Multi
