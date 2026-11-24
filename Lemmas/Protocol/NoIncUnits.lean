-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.CpAsyncPhase
public import Lemmas.Protocol.NoIncRing
public import Lemmas.Protocol.KindRing

@[expose] public section

/-! # The counted arrive-ons of a no-increment object

A proof tool: the arrive-ons of a `NoIncObject` by `N` producer threads, numbered per thread by its
earlier arrive-ons on the object (`NoInc.it`), as counted units (`NoInc.counted`): every phase a
poll observes holds `N` of them (`NoInc.card_phase`). -/

namespace PTX.MbarRing.NoInc

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {N : Nat} {prod : Fin N → Nat}

/-- Producer `a`'s arrive-on on `m` with `t` earlier ones. -/
def op (X : Execution) (m : Loc) (prod : Fin N → Nat) (a : Fin N) (t : Nat) : EvId :=
  (prod a, nthEv X (arriveOnTo m) (prod a) t)

/-- Its completion. -/
def it (X : Execution) (m : Loc) (prod : Fin N → Nat) (a : Fin N) (t : Nat) : Ref :=
  .async (op X m prod a t) .arriveOn

open Classical in
/-- The counted units: those with a fault-free record. -/
def S (X : Execution) (m : Loc) (prod : Fin N → Nat) : Finset (Fin N × Nat) :=
  (Finset.univ ×ˢ Finset.range (Unit.bound X prod)).filter fun x =>
    ∃ r ∈ X.objects m, r.id = it X m prod x.1 x.2 ∧ r.fault = none ∧ r.action = .arrive 1 0

/-- A counted unit's record and arrive-on. -/
theorem S_rec (o : NoIncObject X m N) {x : Fin N × Nat} (hx : x ∈ S X m prod) :
    (∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it X m prod x.1 x.2 ∧
      r.fault = none ∧ r.action = .arrive 1 0) ∧
    (∃ pc, X.get (op X m prod x.1 x.2) = some ⟨pc, .asyncArrive m true⟩) ∧
    ((X.tr (prod x.1)).take (op X m prod x.1 x.2).2).countP (arriveOnTo m) = x.2 ∧
    X.async.arrived (op X m prod x.1 x.2) = true := by
  obtain ⟨-, r, hr, hid, hf, ha⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨-, -, j, hj, ⟨pc, he⟩, harr⟩ := o.arrive_source hk ha
  have hji : j = op X m prod x.1 x.2 := by
    rw [hid] at hj
    exact ((Ref.async.injEq _ _ _ _).mp hj).1.symm
  subst hji
  exact ⟨⟨k, r, hk, hid, hf, ha⟩, ⟨pc, he⟩, (nthEv_spec_of_get he).2, harr⟩

/-- A fault-free arrival record is a counted unit's. -/
theorem rec_S (o : NoIncObject X m N) (hsrc : ∀ i, X.AsyncArrive i m true → ∃ a, i.1 = prod a)
    {k c tx : Nat} {r : Record Ref} (hr : (X.objects m)[k]? = some r) (hf : r.fault = none)
    (ha : r.action = .arrive c tx) : ∃ x ∈ S X m prod, r.id = it X m prod x.1 x.2 := by
  classical
  obtain ⟨rfl, rfl, ⟨g, i⟩, hid, hi, -⟩ := o.arrive_source hr ha
  obtain ⟨a, hga⟩ := hsrc _ hi
  simp only at hga
  subst hga
  obtain ⟨pc, he⟩ := hi
  have hp : arriveOnTo m ⟨pc, .asyncArrive m true⟩ = true := arriveOnTo_of rfl
  set t := ((X.tr (prod a)).take i).countP (arriveOnTo m) with ht
  have hit : it X m prod a t = .async (prod a, i) .arriveOn := by
    simp only [it, op, ht]
    rw [nthEv_eq he hp]
  have hlt : t < Unit.bound X prod := by
    have h1 := len_of_get he
    have h2 : t ≤ i := (List.countP_le_length).trans (List.length_take_le _ _)
    have h3 := Finset.single_le_sum (f := fun a => (X.tr (prod a)).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    simp only at h1 h3
    unfold Unit.bound
    omega
  exact ⟨(a, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_range.mpr hlt⟩, r, List.mem_of_getElem? hr, by rw [hid, hit], hf, ha⟩,
    by rw [hid, hit]⟩

theorem counted (o : NoIncObject X m N) : Counted X m (S X m prod) (it X m prod) where
  record x hx := by
    obtain ⟨⟨k, r, hk, hid, hf, ha⟩, -⟩ := S_rec o hx
    exact ⟨k, r, hk, hid, hf, by rw [ha]; trivial⟩
  init := ⟨N, o.init⟩
  noInval := o.noInval

open Classical in
/-- **The phase a poll observes holds `N` counted units.** -/
theorem card_phase (hX : Consistent L K A mem0 X) (o : NoIncObject X m N)
    (hsrc : ∀ i, X.AsyncArrive i m true → ∃ a, i.1 = prod a) {g n δ : Nat} (hδ' : δ ≤ 1)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ) (hδ : δ ≤ n)
    (hn : n < okPolls m (X.tr g)) :
    N ≤ ((S X m prod).filter
      (fun x => Counted.ph X m (it X m prod) x = Unit.obsOf X m g n)).card := by
  obtain ⟨kw, w, st, hkw, -, -, -, hst, hpos, -, hoo⟩ :=
    (counted (prod := prod) o).poll_obs hX hδ' hAlt hδ hn
  have hch := X.objects_checked hX m
  have hcard := o.completed_count hX (List.getElem?_eq_some_iff.mp hkw).1.le hst
    (q := st.phase - 1) (by omega)
  refine le_trans (le_of_eq hcard.symm) ?_
  refine PairTmaRing.card_le_of_rel _ _
    (fun k x => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m prod x.1 x.2)
    (fun k hk => ?_) (fun k _ k' _ x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hk
  obtain ⟨x, hx, hid⟩ := rec_S o hsrc hr hf ha
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, r, hr, hid⟩
  unfold Counted.ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph, hoo]

end
end PTX.MbarRing.NoInc
