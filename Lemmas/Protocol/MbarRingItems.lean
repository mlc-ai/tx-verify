-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarRingRound
public import Lemmas.Order.DependencyWitness

@[expose] public section

/-! # Round attribution for a ring slot whose full objects count items of several kinds

A proof tool, the generalisation of `MbarRing.Round.Slot` to the shapes of production rings.
A slot has `nf` full objects; consumer `b` polls full object `owner b`. A phase of full object
`f` is completed by items of `nk f` kinds: kind `k` is issued by producer `ownF f k`, which
for its use `s` performs an operation `opF f k s` (an arrival, a copy issue, a commit) that its
polls for the uses `1, …, s` guard (`Resumes`), and whose record on `f` is `itF f k s` (the
operation itself, or its asynchronous notification, which it precedes in the dependency order
`DepStep`). Producer `a` polls its
own empty object `E a`, which the consumers' notifications complete: consumer `b`'s operation
`cm b t` for its use `t`, guarded by its polls of its full object for the uses `0, …, t`,
precedes its notification `note b a t` of `E a` in the dependency order.

Each object is read only through its own history, as in `MbarRing.Round.Slot`: the counted
items `SF f` with their phases `phF f`, the counted notifications `SE a` with their phases
`phE a`; a successful poll observes some completed phase and every counted item of it, as a
`Witness` of the poll (`obsF`, `obsE`); an observed phase holds at least one item of each kind
(`fullF`), or one notification of each consumer (`fullE`); a poller's later polls observe later
phases (`ltF`, `ltE`). Every producer issues an item of every full object (`cover`).

Results, from the acyclicity of the dependency order alone: consumer `b`'s poll for use `j`
observes a phase that holds exactly the items of use `j`, one of each kind (`content_full`,
`observes_full`), and producer `a`'s poll for use `n + 1` exactly the notifications of use `n`
(`content_empty`, `observes_empty`). From `DependencyOk.acyclic` (DEP-ORDER, with the object's
order): an item of use `s` is after every consumer's poll for a use `j < s` in any object's
history (`not_before_full`), a notification of use `t` after producer `a`'s polls for the uses
`1, …, t` (`not_before_empty`), and the polls find their phase numbers (`full_poll_phase`,
`empty_poll_phase`). -/

namespace PTX.MbarRing.Items

open AsyncCopy

/-- Counting on one object: when the phases `o 0 < o 1 < … < o J` each hold at least `|κ|`
items and the items of phase `o j` have uses at most `j`, phase `o j` holds exactly the items
`(k, j)`. -/
theorem content {κ : Type} [Fintype κ] [DecidableEq κ] (S : Finset (κ × Nat))
    (ph : κ × Nat → Nat) (o : Nat → Nat) (J : Nat)
    (hlt : ∀ j j', j < j' → j' ≤ J → o j < o j')
    (hfull : ∀ j ≤ J, Fintype.card κ ≤ (S.filter (fun x => ph x = o j)).card)
    (hle : ∀ j ≤ J, ∀ x ∈ S, ph x = o j → x.2 ≤ j) :
    ∀ j ≤ J, (∀ x ∈ S, ph x = o j → x.2 = j) ∧ ∀ k, (k, j) ∈ S ∧ ph (k, j) = o j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have h1 : ∀ x ∈ S, ph x = o j → x.2 = j := by
      intro x hx hp
      have hle' := hle j hj x hx hp
      by_contra hne
      have hlt' : x.2 < j := by omega
      obtain ⟨-, h2⟩ := ih x.2 hlt' (by omega)
      have := (h2 x.1).2
      rw [Prod.mk.eta, hp] at this
      have := hlt x.2 j hlt' hj
      omega
    refine ⟨h1, fun k => ?_⟩
    have hsub : S.filter (fun x => ph x = o j) ⊆ Finset.univ ×ˢ {j} := by
      intro x hx
      obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr (h1 x hxS hxp)⟩
    have heq : S.filter (fun x => ph x = o j) = Finset.univ ×ˢ {j} :=
      Finset.eq_of_subset_of_card_le hsub (by simpa using hfull j hj)
    have hmem : (k, j) ∈ S.filter (fun x => ph x = o j) :=
      heq ▸ Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩
    exact Finset.mem_filter.mp hmem

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- A ring slot whose full objects count items of several kinds. -/
structure Ring (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (np nc nf : Nat) (nk : Fin nf → Nat) where
  owner : Fin nc → Fin nf
  ownF : (f : Fin nf) → Fin (nk f) → Fin np
  wE : Fin np → Nat → EvId
  opF : (f : Fin nf) → Fin (nk f) → Nat → EvId
  itF : (f : Fin nf) → Fin (nk f) → Nat → Ref
  wF : Fin nc → Nat → EvId
  cm : Fin nc → Nat → EvId
  note : Fin nc → Fin np → Nat → Ref
  SF : (f : Fin nf) → Finset (Fin (nk f) × Nat)
  phF : (f : Fin nf) → Fin (nk f) × Nat → Nat
  SE : Fin np → Finset (Fin nc × Nat)
  phE : Fin np → Fin nc × Nat → Nat
  /-- The completed phase of `F (owner b)` observed by consumer `b`'s poll for use `j`. -/
  oF : Fin nc → Nat → Nat
  /-- The completed phase of `E a` observed by producer `a`'s poll for use `n ≥ 1`. -/
  oE : Fin np → Nat → Nat
  /-- Every producer issues an item of every full object. -/
  cover : ∀ f a, ∃ k, ownF f k = a
  /-- Thread layer: a producer's polls for the uses `1, …, s` guard its operation of use `s`. -/
  guardP : ∀ f, ∀ x ∈ SF f, ∀ n, 1 ≤ n → n ≤ x.2 →
    Resumes K X (wE (ownF f x.1) n) (opF f x.1 x.2)
  /-- The operation precedes its item's record in the dependency order. -/
  issueF : ∀ f, ∀ x ∈ SF f, Relation.ReflTransGen (DepStep L K X)
    (.thread (opF f x.1 x.2), false) (itF f x.1 x.2, false)
  /-- Thread layer: a consumer's polls for the uses `0, …, t` guard its operation of use `t`. -/
  guardM : ∀ a, ∀ y ∈ SE a, ∀ j ≤ y.2, Resumes K X (wF y.1 j) (cm y.1 y.2)
  /-- The consumer's operation precedes its notification in the dependency order. -/
  issue : ∀ a, ∀ y ∈ SE a, Relation.ReflTransGen (DepStep L K X)
    (.thread (cm y.1 y.2), false) (note y.1 a y.2, false)
  /-- Object `F (owner b)`: the poll observes every counted item of the phase it observes. -/
  obsF : ∀ b j, X.RefPresent (.thread (wF b j)) → ∀ x ∈ SF (owner b),
    phF (owner b) x = oF b j → Witness L X (itF (owner b) x.1 x.2) (wF b j)
  /-- Object `E a`: the poll observes every counted notification of the phase it observes. -/
  obsE : ∀ a n, 1 ≤ n → X.RefPresent (.thread (wE a n)) → ∀ y ∈ SE a, phE a y = oE a n →
    Witness L X (note y.1 a y.2) (wE a n)
  /-- Object `F (owner b)`: an observed phase holds at least one item of each kind. -/
  fullF : ∀ b j, X.RefPresent (.thread (wF b j)) →
    nk (owner b) ≤ ((SF (owner b)).filter (fun x => phF (owner b) x = oF b j)).card
  /-- Object `E a`: an observed phase holds at least `nc` counted notifications. -/
  fullE : ∀ a n, 1 ≤ n → X.RefPresent (.thread (wE a n)) →
    nc ≤ ((SE a).filter (fun y => phE a y = oE a n)).card
  /-- Object `F (owner b)`: a consumer's earlier poll is present and observed an earlier phase. -/
  ltF : ∀ b j j', j < j' → X.RefPresent (.thread (wF b j')) →
    X.RefPresent (.thread (wF b j)) ∧ oF b j < oF b j'
  /-- Object `E a`: the producer's earlier poll is present and observed an earlier phase. -/
  ltE : ∀ a n n', 1 ≤ n → n < n' → X.RefPresent (.thread (wE a n')) →
    X.RefPresent (.thread (wE a n)) ∧ oE a n < oE a n'

namespace Ring
variable {np nc nf : Nat} {nk : Fin nf → Nat} (R : Ring L K A X np nc nf nk)

/-- Every consumer's poll for a use below `s` precedes item `x` of full object `f`. -/
def ReachF (f : Fin nf) (x : Fin (nk f) × Nat) : Prop :=
  ∀ b j, j < x.2 →
    Relation.TransGen (DepStep L K X) (.thread (R.wF b j), true) (R.itF f x.1 x.2, false)

/-- Producer `a`'s polls for the uses `1, …, t` precede consumer `y.1`'s notification of use
`t`. -/
def ReachE (a : Fin np) (y : Fin nc × Nat) : Prop :=
  ∀ n, 1 ≤ n → n ≤ y.2 →
    Relation.TransGen (DepStep L K X) (.thread (R.wE a n), true) (R.note y.1 a y.2, false)

/-- The phases observed by producer `a`'s polls `1, …, s` hold the notifications of the uses
`0, …, s - 1`, when the notifications they observe are of uses below the poll. -/
theorem content_empty_of {a : Fin np} {s : Nat}
    (hpres : ∀ n, 1 ≤ n → n ≤ s → X.RefPresent (.thread (R.wE a n)))
    (hle : ∀ n, 1 ≤ n → n ≤ s → ∀ y ∈ R.SE a, R.phE a y = R.oE a n → y.2 + 1 ≤ n) :
    ∀ m, m + 1 ≤ s → (∀ y ∈ R.SE a, R.phE a y = R.oE a (m + 1) → y.2 = m) ∧
      ∀ b, (b, m) ∈ R.SE a ∧ R.phE a (b, m) = R.oE a (m + 1) := by
  cases s with
  | zero => intro m hm; omega
  | succ s =>
    have h := content (R.SE a) (R.phE a) (fun m => R.oE a (m + 1)) s
      (fun j j' hjj hj' => (R.ltE a (j + 1) (j' + 1) (by omega) (by omega)
        (hpres (j' + 1) (by omega) (by omega))).2)
      (fun j hj => by
        simpa using R.fullE a (j + 1) (by omega) (hpres (j + 1) (by omega) (by omega)))
      (fun j hj y hy hp => by have := hle (j + 1) (by omega) (by omega) y hy hp; omega)
    exact fun m hm => h m (by omega)

/-- The phases observed by consumer `b`'s polls `0, …, t` hold the items of the uses `0, …, t`,
when the items they observe are of uses at most the poll's. -/
theorem content_full_of {b : Fin nc} {t : Nat} (hpres : X.RefPresent (.thread (R.wF b t)))
    (hle : ∀ j ≤ t, ∀ x ∈ R.SF (R.owner b), R.phF (R.owner b) x = R.oF b j → x.2 ≤ j) :
    ∀ j ≤ t, (∀ x ∈ R.SF (R.owner b), R.phF (R.owner b) x = R.oF b j → x.2 = j) ∧
      ∀ k, (k, j) ∈ R.SF (R.owner b) ∧ R.phF (R.owner b) (k, j) = R.oF b j := by
  have hp : ∀ j ≤ t, X.RefPresent (.thread (R.wF b j)) := fun j hj => by
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · exact (R.ltF b j t h hpres).1
    · exact hpres
  exact content (R.SF (R.owner b)) (R.phF (R.owner b)) (R.oF b) t
    (fun j j' hjj hj' => (R.ltF b j j' hjj (hp j' hj')).2)
    (fun j hj => by simpa using R.fullF b j (hp j hj)) hle

/-- The dependency paths, by well-founded induction along the dependency order. -/
theorem reach (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) :
    (∀ f, ∀ x ∈ R.SF f, R.ReachF f x) ∧ ∀ a, ∀ y ∈ R.SE a, R.ReachE a y := by
  classical
  let nodeF : (f : Fin nf) → Fin (nk f) × Nat → Ref × Bool := fun f x => (R.itF f x.1 x.2, false)
  let nodeE : Fin np → Fin nc × Nat → Ref × Bool := fun a y => (R.note y.1 a y.2, false)
  let nodes : Finset (Ref × Bool) :=
    Finset.univ.biUnion (fun f => (R.SF f).image (nodeF f)) ∪
      Finset.univ.biUnion (fun a => (R.SE a).image (nodeE a))
  let P : Ref × Bool → Prop := fun n =>
    (∀ f, ∀ x ∈ R.SF f, n = nodeF f x → R.ReachF f x) ∧
      ∀ a, ∀ y ∈ R.SE a, n = nodeE a y → R.ReachE a y
  have hmemF : ∀ f, ∀ x ∈ R.SF f, nodeF f x ∈ nodes := fun f x hx =>
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hx⟩)
  have hmemE : ∀ a, ∀ y ∈ R.SE a, nodeE a y ∈ nodes := fun a y hy =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hy⟩)
  have hall := induction_of_acyclic hacyc nodes P (fun node _ ih => by
    refine ⟨fun f x hx hn => ?_, fun a y hy hn => ?_⟩
    · -- item `x` of full object `f`, of producer `a = ownF f x.1`
      subst hn
      have hpres : ∀ n, 1 ≤ n → n ≤ x.2 → X.RefPresent (.thread (R.wE (R.ownF f x.1) n)) :=
        fun n h1 h2 => Round.Slot.present_of_guard (R.guardP f x hx n h1 h2)
      have hle : ∀ n, 1 ≤ n → n ≤ x.2 → ∀ y ∈ R.SE (R.ownF f x.1),
          R.phE (R.ownF f x.1) y = R.oE (R.ownF f x.1) n → y.2 + 1 ≤ n := by
        intro n h1 h2 y hy hp
        by_contra hgt
        have hobs := R.obsE _ n h1 (hpres n h1 h2) y hy hp
        have hpath : Relation.TransGen (DepStep L K X) (nodeE (R.ownF f x.1) y) (nodeF f x) :=
          (Relation.TransGen.single (DepStep.of_witness L hobs)).tail
            (DepStep.of_resumes L (R.guardP f x hx n h1 h2)) |>.trans_left (R.issueF f x hx)
        have hr := (ih _ (hmemE _ y hy) hpath).2 _ y hy rfl n h1 (by omega)
        exact hacyc _ (hr.tail (DepStep.of_witness L hobs))
      intro b j hj
      obtain ⟨hyS, hyp⟩ := (R.content_empty_of hpres hle j (by omega)).2 b
      exact ((((Relation.TransGen.single
          (DepStep.of_resumes L (R.guardM _ (b, j) hyS j le_rfl))).trans_left
        (R.issue _ (b, j) hyS)).tail
        (DepStep.of_witness L (R.obsE _ (j + 1) (by omega) (hpres (j + 1) (by omega) (by omega))
          (b, j) hyS hyp))).tail
        (DepStep.of_resumes L (R.guardP f x hx (j + 1) (by omega) (by omega)))).trans_left
        (R.issueF f x hx)
    · -- notification `y = (b, t)` of `E a`
      subst hn
      have hpres : X.RefPresent (.thread (R.wF y.1 y.2)) :=
        Round.Slot.present_of_guard (R.guardM a y hy y.2 le_rfl)
      have hle : ∀ j ≤ y.2, ∀ x ∈ R.SF (R.owner y.1),
          R.phF (R.owner y.1) x = R.oF y.1 j → x.2 ≤ j := by
        intro j hj x hx hp
        by_contra hgt
        have hobs := R.obsF y.1 j (Round.Slot.present_of_guard (R.guardM a y hy j hj)) x hx hp
        have hpath : Relation.TransGen (DepStep L K X) (nodeF (R.owner y.1) x) (nodeE a y) :=
          ((Relation.TransGen.single (DepStep.of_witness L hobs)).tail
            (DepStep.of_resumes L (R.guardM a y hy j hj))).trans_left (R.issue a y hy)
        have hr := (ih _ (hmemF _ x hx) hpath).1 _ x hx rfl y.1 j (by omega)
        exact hacyc _ (hr.tail (DepStep.of_witness L hobs))
      intro n h1 h2
      obtain ⟨k, hk⟩ := R.cover (R.owner y.1) a
      obtain ⟨hxS, hxp⟩ := (R.content_full_of hpres hle n h2).2 k
      have hg := R.guardP (R.owner y.1) (k, n) hxS n h1 le_rfl
      rw [hk] at hg
      exact ((((Relation.TransGen.single (DepStep.of_resumes L hg)).trans_left
        (R.issueF _ (k, n) hxS)).tail
        (DepStep.of_witness L (R.obsF y.1 n (Round.Slot.present_of_guard (R.guardM a y hy n h2))
          (k, n) hxS
          hxp))).tail (DepStep.of_resumes L (R.guardM a y hy n h2))).trans_left (R.issue a y hy))
  exact ⟨fun f x hx => (hall _ (hmemF f x hx)).1 f x hx rfl,
    fun a y hy => (hall _ (hmemE a y hy)).2 a y hy rfl⟩

/-- Object `F (owner b)`: the poll for use `j` observes a phase holding exactly the counted
items of use `j`, one of each kind. -/
theorem content_full (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {b : Fin nc} {j : Nat}
    (hw : X.RefPresent (.thread (R.wF b j))) :
    (∀ x ∈ R.SF (R.owner b), R.phF (R.owner b) x = R.oF b j → x.2 = j) ∧
      ∀ k, (k, j) ∈ R.SF (R.owner b) ∧ R.phF (R.owner b) (k, j) = R.oF b j := by
  have hr := (R.reach hacyc).1 (R.owner b)
  refine R.content_full_of hw (fun j' hj' x hx hp => ?_) j le_rfl
  by_contra hgt
  have hpres : X.RefPresent (.thread (R.wF b j')) := by
    rcases Nat.lt_or_eq_of_le hj' with h | rfl
    · exact (R.ltF b j' j h hw).1
    · exact hw
  exact hacyc _ ((hr x hx b j' (by omega)).tail (DepStep.of_witness L (R.obsF b j' hpres x hx hp)))

/-- Object `E a`: the poll for use `n + 1` observes a phase holding exactly the counted
notifications of use `n`, one of each consumer. -/
theorem content_empty (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {a : Fin np} {n : Nat}
    (hw : X.RefPresent (.thread (R.wE a (n + 1)))) :
    (∀ y ∈ R.SE a, R.phE a y = R.oE a (n + 1) → y.2 = n) ∧
      ∀ b, (b, n) ∈ R.SE a ∧ R.phE a (b, n) = R.oE a (n + 1) := by
  have hr := (R.reach hacyc).2 a
  have hpres : ∀ k, 1 ≤ k → k ≤ n + 1 → X.RefPresent (.thread (R.wE a k)) := fun k h1 h2 => by
    rcases Nat.lt_or_eq_of_le h2 with h | rfl
    · exact (R.ltE a k (n + 1) h1 h hw).1
    · exact hw
  refine R.content_empty_of hpres (fun k h1 h2 y hy hp => ?_) n le_rfl
  by_contra hgt
  exact hacyc _ ((hr y hy k h1 (by omega)).tail
    (DepStep.of_witness L (R.obsE a k h1 (hpres k h1 h2) y hy hp)))

/-- The consumer's poll for use `j` observed the counted item of kind `k` and use `j`. -/
theorem observes_full (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {b : Fin nc} {j : Nat}
    (hw : X.RefPresent (.thread (R.wF b j))) (k : Fin (nk (R.owner b))) :
    (k, j) ∈ R.SF (R.owner b) ∧
      Witness L X (R.itF (R.owner b) k j) (R.wF b j) := by
  obtain ⟨hS, hp⟩ := (R.content_full hacyc hw).2 k
  exact ⟨hS, R.obsF b j hw (k, j) hS hp⟩

/-- The producer's poll for use `n + 1` observed consumer `b`'s counted notification of use
`n`. -/
theorem observes_empty (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {a : Fin np} {n : Nat}
    (hw : X.RefPresent (.thread (R.wE a (n + 1)))) (b : Fin nc) :
    (b, n) ∈ R.SE a ∧ Witness L X (R.note b a n) (R.wE a (n + 1)) := by
  obtain ⟨hS, hp⟩ := (R.content_empty hacyc hw).2 b
  exact ⟨hS, R.obsE a (n + 1) (by omega) hw (b, n) hS hp⟩

/-- An operation guarded by producer `a`'s polls `1, …, s` is preceded by every consumer's poll
for a use below `s`, which is present. -/
theorem reach_op (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) {a : Fin np} {s : Nat}
    {op : EvId}
    (hguard : ∀ n, 1 ≤ n → n ≤ s → Resumes K X (R.wE a n) op) (b : Fin nc) {j : Nat}
    (hj : j < s) : X.RefPresent (.thread (R.wF b j)) ∧
      Relation.TransGen (DepStep L K X) (.thread (R.wF b j), true) (.thread op, false) := by
  have hg := hguard (j + 1) (by omega) (by omega)
  obtain ⟨hy, hobs⟩ := R.observes_empty hacyc (Round.Slot.present_of_guard hg) b
  have hgM := R.guardM a (b, j) hy j le_rfl
  exact ⟨Round.Slot.present_of_guard hgM,
    (((Relation.TransGen.single (DepStep.of_resumes L hgM)).trans_left
    (R.issue a (b, j) hy)).tail (DepStep.of_witness L hobs)).tail (DepStep.of_resumes L hg)⟩

/-- An operation guarded by consumer `b`'s polls `0, …, t` is preceded by producer `a`'s polls
for the uses `1, …, t`, which are present. -/
theorem reach_consumer_op (hacyc : ∀ n, ¬ Relation.TransGen (DepStep L K X) n n) (a : Fin np)
    {b : Fin nc}
    {t : Nat} {op : EvId} (hguard : ∀ j ≤ t, Resumes K X (R.wF b j) op) {n : Nat}
    (h1 : 1 ≤ n) (hn : n ≤ t) : X.RefPresent (.thread (R.wE a n)) ∧
      Relation.TransGen (DepStep L K X) (.thread (R.wE a n), true) (.thread op, false) := by
  have hg := hguard n hn
  obtain ⟨k, hk⟩ := R.cover (R.owner b) a
  obtain ⟨hx, hobs⟩ := R.observes_full hacyc (Round.Slot.present_of_guard hg) k
  have hgP := R.guardP _ (k, n) hx n h1 le_rfl
  rw [hk] at hgP
  exact ⟨Round.Slot.present_of_guard hgP,
    ((((Relation.TransGen.single (DepStep.of_resumes L hgP)).trans_left
    (R.issueF _ (k, n) hx)).tail (DepStep.of_witness L hobs)).tail (DepStep.of_resumes L hg))⟩

/-- DEP-ORDER on `F f`: a counted item of use `s` is not before, in any object's
history, a consumer's poll for a use `j < s`. -/
theorem not_before_full {mem0 : Mem0} (hX : Consistent L K A mem0 X) {m : Loc} {f : Fin nf}
    {x : Fin (nk f) × Nat} (hx : x ∈ R.SF f) {b : Fin nc} {j : Nat} (hj : j < x.2) :
    ¬ MBarrier.Before (X.objects m) (R.itF f x.1 x.2) (.thread (R.wF b j)) :=
  Round.Slot.not_before_of_reach hX ((R.reach hX.depAcyclic).1 f x hx b j hj)

/-- DEP-ORDER on `E a`: a counted notification of use `t` is not before, in any
object's history, producer `a`'s poll for a use `1 ≤ n ≤ t`. -/
theorem not_before_empty {mem0 : Mem0} (hX : Consistent L K A mem0 X) {m : Loc}
    {a : Fin np} {y : Fin nc × Nat} (hy : y ∈ R.SE a) {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ y.2) :
    ¬ MBarrier.Before (X.objects m) (R.note y.1 a y.2) (.thread (R.wE a n)) :=
  Round.Slot.not_before_of_reach hX ((R.reach hX.depAcyclic).2 a y hy n h1 hn)

/-- Exact phase at `F (owner b)`: consumer `b`'s successful poll for use `j`, with `j + δ`
earlier selected successes of an alternating poller, found phase `j + 1`, so it observed
phase `j`. From the object's checked history: the non-faulting arrivals are unit arrivals of
counted items of the kinds `arr`, and the expected count is `|arr|`. -/
theorem full_poll_phase {mem0 : Mem0} (hX : Consistent L K A mem0 X) {b : Fin nc}
    (arr : Finset (Fin (nk (R.owner b)))) (harr : 0 < arr.card) {m : Loc}
    (hni : MBarrier.NoInval (X.objects m)) (sel : Ref → Bool) {δ : Nat} (hδ : δ ≤ 1)
    (halt : MBarrier.SelectedAlternates sel (X.objects m) δ)
    (hcount : ∀ (k : Nat) (r : MBarrier.Record Ref) (c tx : Nat), (X.objects m)[k]? = some r →
      r.fault = none → r.action = .arrive c tx →
      c = 1 ∧ ∃ x ∈ (R.SF (R.owner b)).filter (fun x => x.1 ∈ arr),
        r.id = R.itF (R.owner b) x.1 x.2)
    (hexp : ∀ k st, MBarrier.stateBefore (X.objects m) k = some st → st.expected = arr.card)
    {j k : Nat} {w : MBarrier.Record Ref} (hk : (X.objects m)[k]? = some w)
    (hwid : w.id = .thread (R.wF b j)) (hww : w.reply.waited = some true)
    (hsel : sel w.id = true) (hcnt : MBarrier.selectedBefore sel (X.objects m) k = j + δ) :
    ∃ st, MBarrier.stateBefore (X.objects m) k = some st ∧ st.phase = j + 1 := by
  classical
  have hch := X.objects_checked hX m
  let S := (R.SF (R.owner b)).filter (fun x => x.1 ∈ arr)
  let upd : Fin (nk (R.owner b)) × Nat → Ref := fun x => R.itF (R.owner b) x.1 x.2
  obtain ⟨st, hst, hph⟩ := hch.selected_poll_phase_of_units hni sel hδ halt hk hsel hww
    (fun st hst => by
      rw [hexp k st hst, hcnt]
      have hu := Round.units_le_of_uses hch upd (S.filter (fun x => x.2 < j + 1)) (i := k)
        (fun k r c tx hr hf ha => (hcount k r c tx hr hf ha).1)
        (fun k' hk' r c tx hr hf ha => by
          obtain ⟨-, x, hx, hid⟩ := hcount k' r c tx hr hf ha
          refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hid⟩
          by_contra hge
          exact R.not_before_full hX (Finset.mem_filter.mp hx).1 (b := b) (j := j) (by omega)
            ⟨k', k, r, w, hr, hid, hk, hwid, hk'⟩)
      have hsub : S.filter (fun x => x.2 < j + 1) ⊆ arr ×ˢ Finset.range (j + 1) := by
        intro x hx
        obtain ⟨hxS, hxj⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hxS).2, Finset.mem_range.mpr hxj⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_range] at hc
      have : arr.card * (j + 1) < arr.card * (j + δ + 2 - δ) :=
        Nat.mul_lt_mul_of_pos_left (by omega) harr
      omega)
  exact ⟨st, hst, by rw [hcnt] at hph; omega⟩

/-- Exact phase at `E a`: producer `a`'s successful poll for use `n ≥ 1`, with `n - 1 + δ`
earlier selected successes of an alternating poller, found phase `n`, so it observed phase
`n - 1`. From `E a`'s checked history: the non-faulting arrivals are the unit notifications of
`SE a`, and the expected count is `nc`. -/
theorem empty_poll_phase {mem0 : Mem0} (hX : Consistent L K A mem0 X) (hnc : 0 < nc) {m : Loc}
    (hni : MBarrier.NoInval (X.objects m)) {a : Fin np} (sel : Ref → Bool) {δ : Nat} (hδ : δ ≤ 1)
    (halt : MBarrier.SelectedAlternates sel (X.objects m) δ)
    (hcount : ∀ (k : Nat) (r : MBarrier.Record Ref) (c tx : Nat), (X.objects m)[k]? = some r →
      r.fault = none → r.action = .arrive c tx → c = 1 ∧ ∃ y ∈ R.SE a, r.id = R.note y.1 a y.2)
    (hexp : ∀ k st, MBarrier.stateBefore (X.objects m) k = some st → st.expected = nc)
    {n k : Nat} {w : MBarrier.Record Ref} (hn : 1 ≤ n) (hk : (X.objects m)[k]? = some w)
    (hwid : w.id = .thread (R.wE a n)) (hww : w.reply.waited = some true)
    (hsel : sel w.id = true) (hcnt : MBarrier.selectedBefore sel (X.objects m) k = n - 1 + δ) :
    ∃ st, MBarrier.stateBefore (X.objects m) k = some st ∧ st.phase = n :=
  Round.poll_phase (X.objects_checked hX m) hni (fun y : Fin nc × Nat => R.note y.1 a y.2) (R.SE a)
    sel hδ halt hcount (by simpa using hexp) ⟨⟨0, hnc⟩⟩ hn hk hww hsel hcnt
    (fun k' hk' r' y hr' _ hy hid' => by
      by_contra hge
      exact R.not_before_empty hX hy (n := n) hn (by omega)
        ⟨k', k, r', w, hr', hid', hk, hwid, hk'⟩)

end Ring
end

end PTX.MbarRing.Items
