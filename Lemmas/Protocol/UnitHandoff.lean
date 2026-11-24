-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.StagingHandoff
public import Lemmas.Protocol.CountNth
public import Lemmas.Flow.Polls

@[expose] public section

/-! # Unit handoffs on one mbarrier object

A proof tool for an mbarrier object on which every producer thread arrives once per use and every
consumer thread polls once per use (FA4's statistics credit and its staged and free output
objects). The *handoff* (`UnitHandoff`) says that a consumer's successful poll with `q + δ`
earlier successful polls of the object synchronizes with every producer's arrival with `q` earlier
arrivals on it: a release arrival that the acquire poll observes, with scopes that meet. `δ` is
the number of successful polls before the first arrival is needed (1 for an object whose
consumers start at parity 1).

The handoff is what the content of the object's phases gives (each phase holds exactly one
arrival of every producer, as `MbarRing.Multi.Units` derives from a reuse gate); a kernel proves
it from its gate. From it, whatever a producer did up to its arrival with `q` earlier arrivals
happens before whatever the consumer does after its poll with `q + δ` earlier polls
(`UnitHandoff.hb`), and so before every consumer event with more than `q + δ` earlier successful
polls (`UnitHandoff.baseCausality_of_counts`). -/

namespace PTX.MbarRing
open PTX.Flow

variable {L : Launch} {X : Execution}

/-- Arrival `x` and successful poll `w` synchronize on `m`: a release arrival, observed by an
acquire poll, with scopes that meet. -/
def Syncs (L : Launch) (X : Execution) (x w : EvId) (m : Loc) : Prop :=
  ∃ rs, MbarRelease X x m rs ∧ ∃ as, AsyncCopy.WaitObserves X (.thread x) w m true as ∧
    ScopesMeet L rs x.1 as w.1

/-- **The unit handoff on `m`** from the producers `prod` to the consumers `cons`, offset `δ`:
a consumer's successful poll of `m` with `q + δ` earlier successful polls of `m` synchronizes with
every producer's arrival on `m` with `q` earlier arrivals on `m`. -/
def UnitHandoff (L : Launch) (X : Execution) (m : Loc) (prod cons : Nat → Prop) (δ : Nat) :
    Prop :=
  ∀ h j pc p acq sc q, cons h → X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩ →
    okPolls m ((X.tr h).take j) = q + δ → ∀ g, prod g →
      ∃ i, arrivals m ((X.tr g).take i) = q ∧ Syncs L X (g, i) (h, j) m

/-- The arrival of a synchronization is an arrival on its object. -/
theorem Syncs.arrives {x w : EvId} {m : Loc} (h : Syncs L X x w m) :
    ∃ ev, X.get x = some ev ∧ arrivesOn m ev = true := by
  obtain ⟨rs, ⟨tx, cnt, pc, hx⟩, -⟩ := h
  exact ⟨_, hx, by simp [arrivesOn, sourceArrive]⟩

/-- An arrival on `m` past index `e` of a thread with no more than `q` arrivals on `m` before
`e` is at or after `e` when it has exactly `q` earlier ones. -/
theorem arrival_index_ge {g e i q : Nat} {m : Loc} {ev : Event}
    (hev : X.get (g, i) = some ev) (ha : arrivesOn m ev = true)
    (hi : arrivals m ((X.tr g).take i) = q) (he : arrivals m ((X.tr g).take e) ≤ q) :
    e ≤ i := by
  by_contra hlt
  have hs : arrivals m ((X.tr g).take (i + 1)) = q + 1 := by
    have hg : (X.tr g)[i]? = some ev := hev
    simp only [arrivals] at hi ⊢
    rw [List.take_add_one, hg, Option.toList_some, List.countP_append, hi]
    simp [ha]
  have hm := (List.take_sublist_take_left (l := X.tr g) (by omega : i + 1 ≤ e)).countP_le
    (p := arrivesOn m)
  simp only [arrivals] at hs he
  omega

namespace UnitHandoff

variable {m : Loc} {prod cons : Nat → Prop} {δ : Nat}

/-- A handoff holds for fewer producers and consumers. -/
theorem mono (hU : UnitHandoff L X m prod cons δ) {prod' cons' : Nat → Prop}
    (hp : ∀ g, prod' g → prod g) (hc : ∀ h, cons' h → cons h) :
    UnitHandoff L X m prod' cons' δ :=
  fun h j pc p acq sc q hh hw hq g hg => hU h j pc p acq sc q (hc h hh) hw hq g (hp g hg)

/-- **A producer's events up to its arrival happen before the consumer's events after its
poll.** Event `e` of producer `g` has no more than `q` arrivals on `m` before it; event `f` of
consumer `h` follows its poll with `q + δ` earlier successful polls. -/
theorem hb (hU : UnitHandoff L X m prod cons δ) {h j pc p q g e f : Nat} {acq : Bool}
    {sc : MbarScope}
    (hh : cons h) (hw : X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩)
    (hq : okPolls m ((X.tr h).take j) = q + δ) (hg : prod g)
    (he : arrivals m ((X.tr g).take e) ≤ q) (hf : j < f) (hfl : f < (X.tr h).length) :
    PTX.baseCausality L X (g, e) (h, f) := by
  obtain ⟨i, hi, hs⟩ := hU h j pc p acq sc q hh hw hq g hg
  obtain ⟨ev, hev, ha⟩ := hs.arrives
  have hle := arrival_index_ge hev ha hi he
  obtain ⟨rs, hrel, as, hobs, hsc⟩ := hs
  exact Staging.baseCausality_of_handoff hrel hobs hsc ⟨rfl, hle⟩ ⟨rfl, hf, hfl⟩

/-- A thread with more than `c` successful polls of `m` before `f` has the one with `c` earlier
ones before `f`. -/
theorem exists_poll {h f c : Nat} (hc : c + 1 ≤ okPolls m ((X.tr h).take f)) :
    ∃ j pc p acq sc, j < f ∧ X.get (h, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr h).take j) = c := by
  obtain ⟨j, ev, hj, hp, hcnt⟩ := Slot.exists_nth_countP (okPoll m) hc
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcnt
  have hget : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pc, kind⟩ := ev
  cases kind with
  | wait target p ok acq sc =>
    cases ok <;> simp only [okPoll, sourceWaitSuccess, decide_eq_true_eq,
      Bool.false_eq_true] at hp
    subst hp
    exact ⟨j, pc, p, acq, sc, hjf, hget, hcnt⟩
  | _ => simp [okPoll, sourceWaitSuccess] at hp

/-- **A producer's events up to its arrival happen before every consumer event with more
successful polls**: event `e` of producer `g` has no more than `q` arrivals on `m` before it, and
consumer `h` has more than `q + δ` successful polls of `m` before `f`. -/
theorem baseCausality_of_counts (hU : UnitHandoff L X m prod cons δ) {h g e f q : Nat} (hh : cons h)
    (hg : prod g) (he : arrivals m ((X.tr g).take e) ≤ q)
    (hf : q + δ + 1 ≤ okPolls m ((X.tr h).take f)) (hfl : f < (X.tr h).length) :
    PTX.baseCausality L X (g, e) (h, f) := by
  obtain ⟨j, pc, p, acq, sc, hjf, hw, hq⟩ := exists_poll hf
  exact hU.hb hh hw hq hg he hjf hfl

end UnitHandoff

end PTX.MbarRing
