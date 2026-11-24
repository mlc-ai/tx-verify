-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MultiObs
public import Lemmas.Order.WaitOrderObject
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The reuse paths of a family of objects, by one induction along the dependency order

A proof tool, generic over the kernel (the kernel-free part of FA4's
`Proof/Protocol/TmemReach*.lean`). The reuse paths (`Unit.Reach`, `Notify.Reach`) of objects whose
producers wait on each other's objects are proved together: the observation step of one object
(a consumer's poll sees the unit of its use, `Multi.Obs.content_of_reach`) needs the paths of the
units its polls observe, which are another object's paths at an earlier node.

* **The nodes** (`nodes`): the issues of the thread events of the launch and their commit
  notifications; every producer event of a unit object and every notification of a commit object
  is one (`thread_mem`, `notify_mem`).
* **The joint induction** (`joint`): a family of goals `G i n` (`i` names an object and a
  consumer; `n` a node), each proved at a node from all the goals at the nodes before it, holds
  at every node.
* **The goals and their exports**: `UnitAt` and `NotifyAt` are the paths of a unit or commit
  object that end at a node; at every node they are the object's reuse paths (`unit_reach`,
  `notify_reach`).
* **The step's tools**: inside the induction a consumer's poll that precedes the node observes the
  unit of its use (`unit_content`, `notify_content`, from the goals at the earlier nodes); a
  canonical spin's successful poll resumes the thread's later events (`poll_guard`); a commit
  precedes its notification (`commit_notify`); a record of a notification is a present commit's
  (`notify_rec`).

A kernel's reuse proof is then its route facts: per object, which earlier poll of which object
precedes a producer event of each use (the chains of `TmemReach`'s `stepP`, `stepS`, `stepO`). -/

namespace PTX.MbarRing.Reach

open AsyncCopy Flow

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-! ### The nodes -/

/-- The thread events of the launch (with a bound on the trace lengths). -/
def evs (L : Launch) (X : Execution) : Finset EvId :=
  Finset.range L.threads ×ˢ
    Finset.range (∑ g ∈ Finset.range L.threads, (X.tr g).length + 1)

open Classical in
/-- The nodes of the induction: the issues of the thread events and their commit
notifications. -/
def nodes (L : Launch) (X : Execution) : Finset (Ref × Bool) :=
  (evs L X).image (fun e => ((.thread e : Ref), false)) ∪
    (evs L X ×ˢ (Finset.univ : Finset (Fin 16))).image
      (fun q => ((.async q.1 (.tcNotify q.2) : Ref), false))

theorem evs_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : e ∈ evs L X := by
  have hg := PTX.Proof.event_thread_lt hX he
  have hl := len_of_get he
  have h3 := Finset.single_le_sum (f := fun g => (X.tr g).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hg)
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hg, Finset.mem_range.mpr (by omega)⟩

theorem thread_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : ((.thread e : Ref), false) ∈ nodes L X := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (evs_mem hX he))

theorem notify_mem (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event} (rank : Fin 16)
    (he : X.get e = some ev) : ((.async e (.tcNotify rank) : Ref), false) ∈ nodes L X := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e, rank),
    Finset.mem_product.mpr ⟨evs_mem hX he, Finset.mem_univ _⟩, rfl⟩)

/-! ### The joint induction -/

/-- **A family of goals proved node by node from the goals at the earlier nodes holds at every
node** (the dependency order is acyclic, DEP-ORDER). -/
theorem joint (hX : Consistent L K A mem0 X) {ι : Type} (G : ι → Ref × Bool → Prop)
    (step : ∀ n ∈ nodes L X, (∀ n' ∈ nodes L X, Relation.TransGen (DepStep L K X) n' n →
      ∀ i, G i n') → ∀ i, G i n) :
    ∀ i, ∀ n ∈ nodes L X, G i n := fun i n hn =>
  induction_of_acyclic (DepStepAcyclic.of_dependency hX.dependency) (nodes L X)
    (fun n => ∀ i, G i n) step n hn i

/-! ### The goals and their exports -/

/-- The reuse paths of unit object `m` (producers `prod`, offset `δ`) as thread `g` polls it,
that end at node `n`. -/
def UnitAt (L : Launch) (K : Kernel) (X : Execution) (m : Loc) (N : Nat) (prod : Fin N → Nat)
    (δ g : Nat) (n : Ref × Bool) : Prop :=
  ∀ x ∈ Unit.S X m prod, n = (.thread (Unit.it X m prod x.1 x.2), false) → ∀ j < x.2,
    Relation.TransGen (DepStep L K X) (.thread (g, Poll.nth X m g (j + δ)), true) n

/-- The reuse paths of commit object `m` (committing thread `c`, its view `m0`, offset `δ`) as
thread `h` polls it, that end at node `n`. -/
def NotifyAt (L : Launch) (K : Kernel) (X : Execution) (m : Loc) (c : Nat) (m0 : Loc)
    (δ h : Nat) (n : Ref × Bool) : Prop :=
  ∀ x ∈ Notify.S X m c m0, n = (Notify.it X m c m0 x.2, false) → ∀ j < x.2,
    Relation.TransGen (DepStep L K X) (.thread (h, Poll.nth X m h (j + δ)), true) n

variable {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- **A unit object's reuse paths from the goal at every node.** -/
theorem unit_reach (hX : Consistent L K A mem0 X) (O : Unit.Obj X m N prod δ) {g : Nat}
    (h : ∀ n ∈ nodes L X, UnitAt L K X m N prod δ g n) : Unit.Reach L K A X m N prod δ g := by
  intro x hx j hj
  obtain ⟨-, ⟨pc, sc, hget⟩, -⟩ := O.S_rec hx
  exact h _ (thread_mem hX hget) x hx rfl j hj

/-- **A commit object's reuse paths from the goal at every node.** -/
theorem notify_reach (hX : Consistent L K A mem0 X) {c : Nat} {m0 : Loc}
    (O : Notify.Obj X m c m0 δ) {h : Nat}
    (hG : ∀ n ∈ nodes L X, NotifyAt L K X m c m0 δ h n) : Notify.Reach L K A X m c m0 δ h := by
  intro x hx j hj
  obtain ⟨-, pc, sp, hget, -⟩ := O.S_rec hx
  exact hG _ (notify_mem hX _ hget) x hx rfl j hj

/-! ### The step's tools -/

/-- **A spinning successful poll resumes each later event** with more successful polls before
it. -/
theorem poll_guard
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {g k n : Nat} (hk : k < (X.tr g).length) (h : n + 1 ≤ okPolls m ((X.tr g).take k)) :
    DepStep L K X (.thread (g, Poll.nth X m g n), true) (.thread (g, k), false) :=
  DepStep.of_resumes L (Poll.guard hspin hk h)

/-- **The issue of a commit precedes its notification.** -/
theorem commit_notify {y : EvId} {pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (hy : X.get y = some ⟨pc, .tc (.commit sp)⟩) (hr : rank ∈ X.tcNotified y) :
    DepStep L K X (.thread y, false) (.async y (.tcNotify rank), false) :=
  DepStep.issue ⟨_, hy⟩ hr (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h)

/-- **A record of a notification is a present commit's** targeting the object. -/
theorem notify_rec (hX : Consistent L K A mem0 X) {r : MBarrier.Record Ref}
    {y : EvId} {rank : Fin 16} (hr : r ∈ X.objects m) (hid : r.id = .async y (.tcNotify rank)) :
    ∃ pc sp, X.get y = some ⟨pc, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      rank ∈ X.tcNotified y := by
  have hp := object_record_present hX.tma hr
  rw [hid] at hp
  cases record_source hX.tma.2.2.1 hr with
  | init hid' => rw [hid] at hid'; cases hid'
  | inval hid' => rw [hid] at hid'; cases hid'
  | arrive hid' => rw [hid] at hid'; cases hid'
  | wait hid' => rw [hid] at hid'; cases hid'
  | tensor hid' => rw [hid] at hid'; cases hid'
  | increment hid' => rw [hid] at hid'; cases hid'
  | arriveOn hid' => rw [hid] at hid'; cases hid'
  | bulk hid' => rw [hid] at hid'; cases hid'
  | clc hid' => rw [hid] at hid'; cases hid'
  | commit hid' he ht =>
    rw [hid] at hid'
    cases hid'
    exact ⟨_, _, he, ht, hp⟩

/-- **Inside the induction, a consumer's poll of a unit object that precedes the node observes
each producer's unit of its use**: its arrival is a witness of the poll's return. -/
theorem unit_content (hX : Consistent L K A mem0 X) (O : Unit.Obj X m N prod δ)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {g J : Nat} {n : Ref × Bool} (hJ : J + δ < okPolls m (X.tr g))
    (hpath : Relation.TransGen (DepStep L K X) (.thread (g, Poll.nth X m g (J + δ)), true) n)
    (ih : ∀ n' ∈ nodes L X, Relation.TransGen (DepStep L K X) n' n →
      UnitAt L K X m N prod δ g n')
    (a : Fin N) :
    (a, J) ∈ Unit.S X m prod ∧
      Witness L X (.thread (Unit.it X m prod a J)) (g, Poll.nth X m g (J + δ)) := by
  obtain ⟨t, hS, ht, hw⟩ := (O.obs hX g).content_of_reach
    (DepStepAcyclic.of_dependency hX.dependency) (J := J) (n := n)
    (Poll.nth_present.mpr hJ)
    (fun j hj => Poll.enables_earlier hspin (by omega) hJ hpath)
    (fun x hx hxn j hj => by
      obtain ⟨-, ⟨pc, sc, hget⟩, -⟩ := O.S_rec hx
      exact ih _ (thread_mem hX hget) hxn x hx rfl j hj) a
  change t = J at ht
  subst ht
  exact ⟨hS, hw⟩

/-- **Inside the induction, a consumer's poll of a commit object that precedes the node observes
the notification of the commit of its use.** -/
theorem notify_content (hX : Consistent L K A mem0 X) {c : Nat} {m0 : Loc}
    (O : Notify.Obj X m c m0 δ)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {h J : Nat} {n : Ref × Bool} (hJ : J + δ < okPolls m (X.tr h))
    (hpath : Relation.TransGen (DepStep L K X) (.thread (h, Poll.nth X m h (J + δ)), true) n)
    (ih : ∀ n' ∈ nodes L X, Relation.TransGen (DepStep L K X) n' n →
      NotifyAt L K X m c m0 δ h n') :
    ((0 : Fin 1), J) ∈ Notify.S X m c m0 ∧
      Witness L X (Notify.it X m c m0 J) (h, Poll.nth X m h (J + δ)) := by
  obtain ⟨t, hS, ht, hw⟩ := (O.obs hX h).content_of_reach
    (DepStepAcyclic.of_dependency hX.dependency) (J := J) (n := n)
    (Poll.nth_present.mpr hJ)
    (fun j hj => Poll.enables_earlier hspin (by omega) hJ hpath)
    (fun x hx hxn j hj => by
      obtain ⟨-, pc, sp, hget, -⟩ := O.S_rec hx
      exact ih _ (notify_mem hX _ hget) hxn x hx rfl j hj) 0
  change t = J at ht
  subst ht
  exact ⟨hS, hw⟩

end
end PTX.MbarRing.Reach
