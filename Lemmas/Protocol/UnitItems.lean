-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitObject
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # The items of a unit object

A proof tool for reading a unit object (`Unit.Obj`) as an object of `MbarRing.Items.Ring`. The
item `(a, u)` is producer `a`'s arrival of use `u` (`it`, the arrival with `u` earlier ones), and
the counted items are those with a fault-free record (`S`), each in the phase of its record
(`ph`). Every fault-free arrival record is a counted item's (`rec_S`), and a counted item's event
is a unit release arrival of its use (`S_rec`). A successful poll with at least `δ` earlier ones
observes a completed phase: every counted item of that phase is before it in the object's order
(`ubw`, `observed`), the phase holds `N` counted items (`card_phase`), and a poller's later polls
observe later phases (`Poll.observed_lt`). -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- Producer `a`'s arrival on `m` of use `u`. -/
def it (X : Execution) (m : Loc) (prod : Fin N → Nat) (a : Fin N) (u : Nat) : EvId :=
  (prod a, nthEv X (arrivesOn m) (prod a) u)

/-- A bound on the uses of the producers' arrivals. -/
def bound (X : Execution) (prod : Fin N → Nat) : Nat := ∑ a, (X.tr (prod a)).length + 1

open Classical in
/-- The counted items of `m`: those with a fault-free record. -/
def S (X : Execution) (m : Loc) (prod : Fin N → Nat) : Finset (Fin N × Nat) :=
  (Finset.univ ×ˢ Finset.range (bound X prod)).filter fun x =>
    ∃ r ∈ X.objects m, r.id = .thread (it X m prod x.1 x.2) ∧ r.fault = none ∧
      r.action = .arrive 1 0

/-- The phase of a counted item's record. -/
def ph (X : Execution) (m : Loc) (prod : Fin N → Nat) (x : Fin N × Nat) : Nat :=
  MbarRing.Poll.phaseOf X m (.thread (it X m prod x.1 x.2))

/-- The completed phase observed by thread `g`'s successful poll of `m` with `n` earlier ones. -/
def obsOf (X : Execution) (m : Loc) (g n : Nat) : Nat :=
  MbarRing.Poll.observedOf X m (.thread (g, MbarRing.Poll.nth X m g n))

namespace History

/-- A counted item's record and event: a unit release arrival of its use. -/
theorem S_rec (O : History X m N prod) {x : Fin N × Nat} (hx : x ∈ S X m prod) :
    (∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
      r.id = .thread (it X m prod x.1 x.2) ∧
      r.fault = none ∧ r.action = .arrive 1 0) ∧
    (∃ pc sc, X.get (it X m prod x.1 x.2) = some ⟨pc, .arrive m 0 1 true sc⟩) ∧
    arrivals m ((X.tr (prod x.1)).take (it X m prod x.1 x.2).2) = x.2 := by
  obtain ⟨-, r, hr, hid, hf, ha⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨pc, sc, he⟩ := O.arrive_of_id hk ha hid
  exact ⟨⟨k, r, hk, hid, hf, ha⟩, ⟨pc, sc, he⟩, (nthEv_spec_of_get he).2⟩

/-- A fault-free arrival record is a counted item's. -/
theorem rec_S (O : History X m N prod) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (hf : r.fault = none) (ha : r.action = .arrive c tx) :
    ∃ x ∈ S X m prod, r.id = .thread (it X m prod x.1 x.2) := by
  classical
  obtain ⟨rfl, rfl, a, i, pc, sc, hid, he⟩ := O.arrive_rec hr ha
  have hp : arrivesOn m ⟨pc, .arrive m 0 1 true sc⟩ = true := by simp [arrivesOn, sourceArrive]
  have hit : it X m prod a (arrivals m ((X.tr (prod a)).take i)) = (prod a, i) := by
    simp only [it, arrivals]
    rw [nthEv_eq he hp]
  have hlt : arrivals m ((X.tr (prod a)).take i) < bound X prod := by
    have h1 := len_of_get he
    have h2 : arrivals m ((X.tr (prod a)).take i) ≤ i :=
      (List.countP_le_length).trans (List.length_take_le _ _)
    have h3 := Finset.single_le_sum (f := fun a => (X.tr (prod a)).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    simp only at h1 h3
    unfold bound
    omega
  refine ⟨(a, arrivals m ((X.tr (prod a)).take i)), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hlt⟩, r,
      List.mem_of_getElem? hr, by rw [hid, hit], hf, ha⟩, by rw [hid, hit]⟩

/-- The record of thread `g`'s successful poll with `n ≥ δ` earlier ones, and the completed phase
it observes. -/
theorem poll_obs (hX : Consistent L K A mem0 X) (O : History X m N prod) {g n : Nat}
    (hδ' : δ ≤ 1) (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ)
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr g)) :
    ∃ (k : Nat) (w : Record Ref) (st : State), (X.objects m)[k]? = some w ∧
      w.id = .thread (g, MbarRing.Poll.nth X m g n) ∧
      w.reply.waited = some true ∧ w.fault = none ∧ stateBefore (X.objects m) k = some st ∧
      0 < st.phase ∧ observedAt (X.objects m) k = some (st.phase - 1) ∧
      obsOf X m g n = st.phase - 1 := by
  obtain ⟨k, w, -, hk, hwid, -, hww, hwf, hsel⟩ := MbarRing.Poll.record hX (O.pclean hX) hn
  have hs : objectThreadSelected g w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX m)
    O.noInval hδ' hAlt hk hs hww (by omega)
  refine ⟨k, w, st, hk, hwid, hww, hwf, hst, hpos, ho, ?_⟩
  unfold obsOf
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hk ho

/-- A counted item's record in its phase. -/
theorem S_phase (hX : Consistent L K A mem0 X) (O : History X m N prod) {x : Fin N × Nat}
    (hx : x ∈ S X m prod) :
    ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
      r.id = .thread (it X m prod x.1 x.2) ∧
      r.fault = none ∧ r.action = .arrive 1 0 ∧ phaseAt (X.objects m) k = some (ph X m prod x) := by
  obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := O.S_rec hx
  obtain ⟨-, sd, hsd, -⟩ := PairTmaRing.state_of_init hX O.init O.noInval hk
    (by intro n; rw [ha]; simp)
  have hp : phaseAt (X.objects m) k = some sd.phase := by simp [phaseAt, hsd]
  refine ⟨k, r, hk, hid, hf, ha, ?_⟩
  unfold ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hk hp]
  exact hp

/-- **A poll observes the counted items of its phase**, in the object's order. -/
theorem ubw (hX : Consistent L K A mem0 X) (O : History X m N prod) {g n : Nat}
    (hδ' : δ ≤ 1) (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ)
    (hδ : δ ≤ n)
    (hn : n < okPolls m (X.tr g)) {x : Fin N × Nat} (hx : x ∈ S X m prod)
    (hph : ph X m prod x = obsOf X m g n) :
    UpdateBeforeWait (X.objects m) (.thread (it X m prod x.1 x.2))
      (.thread (g, MbarRing.Poll.nth X m g n)) := by
  obtain ⟨kw, w, st, hkw, hwid, hww, hwf, -, -, ho, hoo⟩ := O.poll_obs hX hδ' hAlt hδ hn
  obtain ⟨k, r, hk, hid, hf, -, hp⟩ := O.S_phase hX hx
  rw [hph, hoo] at hp
  have h := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX m) O.noInval hk hf
    hkw hwf hww hp ho
  rwa [hid, hwid] at h

/-- **A poll observes the counted items of its phase.** -/
theorem observed (hX : Consistent L K A mem0 X) (O : History X m N prod) {g n : Nat}
    (hδ' : δ ≤ 1) (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ)
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr g)) {x : Fin N × Nat} (hx : x ∈ S X m prod)
    (hph : ph X m prod x = obsOf X m g n) :
    Witness L X (.thread (it X m prod x.1 x.2)) (g, MbarRing.Poll.nth X m g n) := by
  obtain ⟨kw, w, st, hkw, hwid, hww, hwf, -, -, ho, hoo⟩ := O.poll_obs hX hδ' hAlt hδ hn
  obtain ⟨k, r, hk, hid, hf, ha, hp⟩ := O.S_phase hX hx
  rw [hph, hoo] at hp
  have hcu : CounterUpdate r.action := by rw [ha]; trivial
  have h := Consistent.observed_of_phase hX O.noInval hk hf hcu hkw hww hp ho
  rw [hid, hwid] at h
  exact Witness.of_mbarObserved h

open Classical in
/-- **The phase a poll observes holds `N` counted items.** -/
theorem card_phase (hX : Consistent L K A mem0 X) (O : History X m N prod) {g n : Nat}
    (hδ' : δ ≤ 1) (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ)
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr g)) :
    N ≤ ((S X m prod).filter (fun x => ph X m prod x = obsOf X m g n)).card := by
  obtain ⟨kw, w, st, hkw, -, -, -, hst, hpos, -, hoo⟩ := O.poll_obs hX hδ' hAlt hδ hn
  have hch := X.objects_checked hX m
  have hcard := hch.card_unit_arrivals_phase O.noInval (n := N) (q := st.phase - 1)
    (fun _ r c tx hr _ ha => (O.arrive_rec hr ha).1)
    (fun _ st' _ hs => PairTmaRing.expected_of_init hX O.init O.noInval hs) O.noIncrement
    (List.getElem?_eq_some_iff.mp hkw).1.le hst (by omega)
  refine le_trans (le_of_eq hcard.symm) ?_
  refine PairTmaRing.card_le_of_rel _ _
    (fun k x => ∃ r, (X.objects m)[k]? = some r ∧ r.id = .thread (it X m prod x.1 x.2))
    (fun k hk => ?_) (fun k _ k' _ x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hk
  obtain ⟨x, hx, hid⟩ := O.rec_S hr hf ha
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, r, hr, hid⟩
  unfold ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph, hoo]

end History

namespace Obj

/-- A counted item's record and event: a unit release arrival of its use. -/
theorem S_rec (O : Obj X m N prod δ) {x : Fin N × Nat} (hx : x ∈ S X m prod) :
    (∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
      r.id = .thread (it X m prod x.1 x.2) ∧
      r.fault = none ∧ r.action = .arrive 1 0) ∧
    (∃ pc sc, X.get (it X m prod x.1 x.2) = some ⟨pc, .arrive m 0 1 true sc⟩) ∧
    arrivals m ((X.tr (prod x.1)).take (it X m prod x.1 x.2).2) = x.2 :=
  O.history.S_rec hx

/-- A fault-free arrival record is a counted item's. -/
theorem rec_S (O : Obj X m N prod δ) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (hf : r.fault = none) (ha : r.action = .arrive c tx) :
    ∃ x ∈ S X m prod, r.id = .thread (it X m prod x.1 x.2) :=
  O.history.rec_S hr hf ha

/-- The record of thread `g`'s successful poll with `n ≥ δ` earlier ones, and the completed phase
it observes. -/
theorem poll_obs (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {g n : Nat}
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr g)) :
    ∃ (k : Nat) (w : Record Ref) (st : State), (X.objects m)[k]? = some w ∧
      w.id = .thread (g, MbarRing.Poll.nth X m g n) ∧
      w.reply.waited = some true ∧ w.fault = none ∧ stateBefore (X.objects m) k = some st ∧
      0 < st.phase ∧ observedAt (X.objects m) k = some (st.phase - 1) ∧
      obsOf X m g n = st.phase - 1 :=
  O.history.poll_obs hX O.δ_le (O.alt hX g) hδ hn

/-- A counted item's record in its phase. -/
theorem S_phase (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {x : Fin N × Nat}
    (hx : x ∈ S X m prod) :
    ∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧
      r.id = .thread (it X m prod x.1 x.2) ∧
      r.fault = none ∧ r.action = .arrive 1 0 ∧ phaseAt (X.objects m) k = some (ph X m prod x) :=
  O.history.S_phase hX hx

/-- **A poll observes the counted items of its phase**, in the object's order. -/
theorem ubw (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {g n : Nat} (hδ : δ ≤ n)
    (hn : n < okPolls m (X.tr g)) {x : Fin N × Nat} (hx : x ∈ S X m prod)
    (hph : ph X m prod x = obsOf X m g n) :
    UpdateBeforeWait (X.objects m) (.thread (it X m prod x.1 x.2))
      (.thread (g, MbarRing.Poll.nth X m g n)) :=
  O.history.ubw hX O.δ_le (O.alt hX g) hδ hn hx hph

/-- **A poll observes the counted items of its phase.** -/
theorem observed (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {g n : Nat}
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr g)) {x : Fin N × Nat} (hx : x ∈ S X m prod)
    (hph : ph X m prod x = obsOf X m g n) :
    Witness L X (.thread (it X m prod x.1 x.2)) (g, MbarRing.Poll.nth X m g n) :=
  O.history.observed hX O.δ_le (O.alt hX g) hδ hn hx hph

/-- **The phase a poll observes holds `N` counted items.** -/
theorem card_phase (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {g n : Nat}
    (hδ : δ ≤ n) (hn : n < okPolls m (X.tr g)) :
    N ≤ ((S X m prod).filter (fun x => ph X m prod x = obsOf X m g n)).card :=
  O.history.card_phase hX O.δ_le (O.alt hX g) hδ hn


end Obj
end
end PTX.MbarRing.Unit
