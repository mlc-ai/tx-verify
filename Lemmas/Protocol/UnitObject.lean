-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Attribution
public import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # An mbarrier object of unit thread arrivals

A proof tool. An object `m` whose every arrival is one thread arrival without transaction bytes,
with release semantics, by one of `N` producer threads `prod a` (`Source.arrive`), and which is
initialized first with count `N` and never invalidated (`Obj`). A producer's arrival is numbered
by its *use*: the producer's arrivals on `m` before it (`arrivals`). Its pollers' successful polls
use the parity of their earlier successful polls plus `δ` (`Obj.parity`).

* A non-faulting arrival record is a producer's unit arrival event (`Obj.arrive_rec`); two
  arrivals of a thread with the same use are one (`arr_index_eq`).
* **A completed phase holds every producer's arrival** (`Obj.phase_all`): every completed phase
  holds `N` unit arrivals (`card_unit_arrivals_phase`); when those have the phase as their use,
  they are of `N` distinct producers, so of each. -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

/-- How a record of a unit object arises. -/
inductive Source (X : Execution) (m : Loc) (prod : Nat → Prop) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g j pc p : Nat} {ok acq : Bool} {sc : MbarScope} (hid : r.id = .thread (g, j))
      (he : X.get (g, j) = some ⟨pc, .wait m p ok acq sc⟩) (ha : r.action = .pollParity p ok)
  | arrive {g j pc : Nat} {sc : MbarScope} (hid : r.id = .thread (g, j)) (hg : prod g)
      (he : X.get (g, j) = some ⟨pc, .arrive m 0 1 true sc⟩) (ha : r.action = .arrive 1 0)

/-- The records of a checked unit-arrival object, independent of which threads poll it. -/
structure History (X : Execution) (m : Loc) (N : Nat) (prod : Fin N → Nat) : Prop where
  pos : 0 < N
  inj : Function.Injective prod
  src : ∀ r ∈ X.objects m, Source X m (fun g => ∃ a, g = prod a) r
  init : PairTmaRing.InitFirst X m N
  noInval : NoInval (X.objects m)

/-- **An object of unit thread arrivals** by the producers `prod`, polled with offset `δ`. -/
structure Obj (X : Execution) (m : Loc) (N : Nat) (prod : Fin N → Nat) (δ : Nat) : Prop where
  pos : 0 < N
  inj : Function.Injective prod
  src : ∀ r ∈ X.objects m, Source X m (fun g => ∃ a, g = prod a) r
  init : PairTmaRing.InitFirst X m N
  noInval : NoInval (X.objects m)
  /-- A successful poll has the parity of its thread's earlier successful polls plus `δ`. -/
  parity : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
    X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩ →
      p % 2 = (okPolls m ((X.tr g).take k) + δ) % 2
  δ_le : δ ≤ 1

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Two arrivals on `m` of a thread with the same use are one. -/
theorem arr_index_eq {g i i' pc pc' tx tx' c c' : Nat} {m : Loc} {rel rel' : Bool}
    {sc sc' : MbarScope} (he : X.get (g, i) = some ⟨pc, .arrive m tx c rel sc⟩)
    (he' : X.get (g, i') = some ⟨pc', .arrive m tx' c' rel' sc'⟩)
    (hu : arrivals m ((X.tr g).take i) = arrivals m ((X.tr g).take i')) : i = i' := by
  have ha : ∀ pc tx c rel sc, arrivesOn m ⟨pc, .arrive m tx c rel sc⟩ = true := by
    intro pc tx c rel sc
    simp [arrivesOn, sourceArrive]
  exact Nat.le_antisymm (arrival_index_ge he' (ha _ _ _ _ _) rfl hu.le)
    (arrival_index_ge he (ha _ _ _ _ _) rfl hu.ge)

namespace History

variable {m : Loc} {N : Nat} {prod : Fin N → Nat}

theorem pclean (hX : Consistent L K A mem0 X) (O : History X m N prod) :
    ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none :=
  PairTmaRing.poll_clean hX O.init O.noInval

/-- An arrival record is a producer's unit arrival event. -/
theorem arrive_rec (O : History X m N prod) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (ha : r.action = .arrive c tx) :
    c = 1 ∧ tx = 0 ∧ ∃ a i pc sc, r.id = .thread (prod a, i) ∧
      X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ := by
  cases O.src r (List.mem_of_getElem? hr) with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive hid hg he ha' =>
    rw [ha] at ha'
    cases ha'
    obtain ⟨a, rfl⟩ := hg
    exact ⟨rfl, rfl, a, _, _, _, hid, he⟩

/-- A record identified by a thread event of a producer is that event's arrival. -/
theorem arrive_of_id (O : History X m N prod) {k c tx i : Nat} {a : Fin N} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (ha : r.action = .arrive c tx)
    (hid : r.id = .thread (prod a, i)) :
    ∃ pc sc, X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ := by
  obtain ⟨-, -, a', i', pc, sc, hid', he⟩ := O.arrive_rec hr ha
  rw [hid] at hid'
  simp only [Ref.thread.injEq, Prod.mk.injEq] at hid'
  obtain ⟨ha', rfl⟩ := hid'
  rw [O.inj ha']
  exact ⟨pc, sc, he⟩

/-- The object has no pending-count increment. -/
theorem noIncrement (O : History X m N prod) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases O.src r hr with
    | init ha | poll _ _ ha | arrive _ _ _ ha => rw [hi] at ha; cases ha

end History

namespace Obj

variable {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- Retain the checked history independently of the consumers' parity discipline. -/
theorem history (O : Obj X m N prod δ) : History X m N prod :=
  ⟨O.pos, O.inj, O.src, O.init, O.noInval⟩

/-- The object's poll records do not fault. -/
theorem pclean (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) :
    ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none :=
  PairTmaRing.poll_clean hX O.init O.noInval

/-- Each thread's successful polls alternate parity with offset `δ`. -/
theorem alt (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) (g : Nat) :
    SelectedAlternates (objectThreadSelected g) (X.objects m) δ :=
  MbarRing.Poll.alternates hX (O.pclean hX) fun _ _ _ _ _ he => O.parity he

theorem arrive_rec (O : Obj X m N prod δ) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (ha : r.action = .arrive c tx) :
    c = 1 ∧ tx = 0 ∧ ∃ a i pc sc, r.id = .thread (prod a, i) ∧
      X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ :=
  O.history.arrive_rec hr ha

theorem arrive_of_id (O : Obj X m N prod δ) {k c tx i : Nat} {a : Fin N} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (ha : r.action = .arrive c tx)
    (hid : r.id = .thread (prod a, i)) :
    ∃ pc sc, X.get (prod a, i) = some ⟨pc, .arrive m 0 1 true sc⟩ :=
  O.history.arrive_of_id hr ha hid

theorem noIncrement (O : Obj X m N prod δ) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  O.history.noIncrement

open Classical in
/-- **A completed phase holds every producer's arrival.** Phase `q` is completed before position
`j`; when the arrivals before `j` in phase `q` have use `q`, producer `a`'s arrival of use `q` is
one of them. -/
theorem phase_all (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {j q : Nat}
    {st : State} (hj : j ≤ (X.objects m).length) (hs : stateBefore (X.objects m) j = some st)
    (hq : q < st.phase)
    (huse : ∀ p < j, ∀ (r : Record Ref) (a : Fin N) (i c tx : Nat), (X.objects m)[p]? = some r →
      r.fault = none → r.action = .arrive c tx → r.id = .thread (prod a, i) →
      phaseAt (X.objects m) p = some q → arrivals m ((X.tr (prod a)).take i) = q)
    (a : Fin N) :
    ∃ p r i, p < j ∧ (X.objects m)[p]? = some r ∧ r.fault = none ∧ r.action = .arrive 1 0 ∧
      r.id = .thread (prod a, i) ∧ phaseAt (X.objects m) p = some q ∧
      arrivals m ((X.tr (prod a)).take i) = q := by
  set log := X.objects m with hlog
  have hch := X.objects_checked hX m
  have hni := O.noInval
  let U := (Finset.range log.length).filter (fun p => UnitArrivalIn log q p)
  have hU : U.card = N := hch.card_unit_arrivals_phase hni (n := N) (q := q)
    (fun p r c tx hr _ ha => (O.arrive_rec hr ha).1)
    (fun p st' _ hs' => PairTmaRing.expected_of_init hX O.init hni hs') O.noIncrement hj hs hq
  have hUj : ∀ p ∈ U, p < j := by
    intro p hp
    obtain ⟨hpl, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hp
    by_contra hge
    obtain ⟨sp, hsp, hle⟩ := hch.phase_mono hni (Nat.le_of_not_lt hge)
      (Finset.mem_range.mp hpl).le hs
    simp only [phaseAt] at hph
    rw [hsp] at hph
    simp only [Option.map_some, Option.some.injEq] at hph
    omega
  let R : Nat → Fin N → Prop := fun p a => ∃ r i, log[p]? = some r ∧ r.id = .thread (prod a, i)
  let T := Finset.univ.filter (fun a : Fin N => ∃ p ∈ U, R p a)
  have hex : ∀ p ∈ U, ∃ a ∈ T, R p a := by
    intro p hp
    obtain ⟨-, r, tx, hr, ha, -, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, a, i, -, -, hid, -⟩ := O.arrive_rec hr ha
    have hR : R p a := ⟨r, i, hr, hid⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, hR⟩, hR⟩
  have huniq : ∀ p ∈ U, ∀ p' ∈ U, ∀ a ∈ T, R p a → R p' a → p = p' := by
    intro p hp p' hp' a _ ⟨r, i, hr, hid⟩ ⟨r', i', hr', hid'⟩
    obtain ⟨-, r0, tx, hr0, ha, hf, hph⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, r0', tx', hr0', ha', hf', hph'⟩ := Finset.mem_filter.mp hp'
    rw [hr] at hr0
    cases hr0
    rw [hr'] at hr0'
    cases hr0'
    have hu := huse p (hUj p hp) r a i 1 tx hr hf ha hid hph
    have hu' := huse p' (hUj p' hp') r' a i' 1 tx' hr' hf' ha' hid' hph'
    obtain ⟨pc, sc, he⟩ := O.arrive_of_id hr ha hid
    obtain ⟨pc', sc', he'⟩ := O.arrive_of_id hr' ha' hid'
    have hii := arr_index_eq he he' (hu.trans hu'.symm)
    subst hii
    exact ObjectInit.checked_record_index_eq hch hr hr' (hid.trans hid'.symm)
  have hle := PairTmaRing.card_le_of_rel U T R hex huniq
  have hNT : N ≤ T.card := hU ▸ hle
  have hT : T = Finset.univ := Finset.eq_univ_of_card T
    (Nat.le_antisymm (by simpa using Finset.card_le_univ T) (by simpa using hNT))
  have haT : a ∈ T := hT ▸ Finset.mem_univ a
  obtain ⟨-, p, hp, r, i, hr, hid⟩ := Finset.mem_filter.mp haT
  obtain ⟨-, r0, tx, hr0, ha, hf, hph⟩ := Finset.mem_filter.mp hp
  rw [hr] at hr0
  cases hr0
  have htx := (O.arrive_rec hr ha).2.1
  subst htx
  exact ⟨p, r, i, hUj p hp, hr, hf, ha, hid, hph, huse p (hUj p hp) r a i 1 0 hr hf ha hid hph⟩

end Obj
end
end PTX.MbarRing.Unit
