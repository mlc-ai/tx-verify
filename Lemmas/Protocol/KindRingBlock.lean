-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.KindRing
public import Lemmas.Protocol.PollLe
public import Lemmas.Protocol.MbarRingBlocker
public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # The phases of a ring slot of kinds at a blocked poll

A proof tool. An item of use `s` of a `KRing` is only issued after every consumer's polls of the
earlier uses (`F_use`), a notification of use `t` after every producer's `t + 1` polls (`E_use`).
So the final phase of the full object is at most a consumer's polls plus one, and that of the empty
object at most a producer's polls (`F_phase_le`, `E_phase_le`: an object's arrival units are
those of its counted items, and its phases hold `N` units each); with the parity of the thread's
next poll the final phase is the thread's polls (`F_phase`), or one less (`E_phase`). -/

namespace PTX.MbarRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A history's arrival units are at most the counted items of its arrivals, and at least the
initial count times the phase. -/
theorem units_bounds (hX : Consistent L K A mem0 X) {m : Loc} {N : Nat}
    (hinit : PairTmaRing.InitFirst X m N) (hni : NoInval (X.objects m))
    (hinc : ∀ r ∈ X.objects m, r.action ≠ .increment)
    (hone : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects m)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → c = 1)
    {κ : Type} {S : Finset (κ × Nat)} {it : κ → Nat → Ref}
    (hrec : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects m)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → ∃ x ∈ S, r.id = it x.1 x.2)
    {st : State} (hst : stateBefore (X.objects m) (X.objects m).length = some st) :
    arrivalUnits (X.objects m) ≤ S.card ∧ N * st.phase ≤ arrivalUnits (X.objects m) := by
  classical
  have hch := X.objects_checked hX m
  constructor
  · rw [arrivalUnits_eq_length (fun r hr c tx hf ha => by
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
        exact hone hk hf ha), ← List.countP_eq_length_filter,
      ← List.take_length (l := X.objects m), MbarRing.Slot.countP_take_card]
    refine PairTmaRing.card_le_of_rel _ _
      (fun k x => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it x.1 x.2)
      (fun k hk => ?_) (fun k _ k' _ x _ h1 h2 => by
        obtain ⟨r, hr, hid⟩ := h1
        obtain ⟨r', hr', hid'⟩ := h2
        exact ObjectInit.checked_record_index_eq hch hr hr' (hid.trans hid'.symm))
    obtain ⟨-, hk'⟩ := Finset.mem_filter.mp hk
    obtain ⟨r, hr, hc⟩ : ∃ r, (X.objects m)[k]? = some r ∧ countedArrive r = true := by
      cases h : (X.objects m)[k]? with
      | none => rw [h] at hk'; simp at hk'
      | some r => rw [h] at hk'; exact ⟨r, rfl, by simpa using hk'⟩
    obtain ⟨hf, c, tx, ha⟩ := countedArrive_iff.mp hc
    obtain ⟨x, hx, hid⟩ := hrec hr hf ha
    exact ⟨x, hx, r, hr, hid⟩
  · obtain ⟨hp, hacc⟩ := (hch.accounted hni le_rfl).2 st hst
    simp only [unitsBefore, List.take_length] at hacc
    rw [incrementsBefore_length_of _ hinc] at hp hacc
    have he := PairTmaRing.expected_of_init hX hinit hni hst
    rw [he] at hp hacc
    have : N * (st.phase + 1) = N * st.phase + N := Nat.mul_succ _ _
    omega

namespace KRing

variable {np nc nk : Nat}

/-- **An item's use is at most every consumer's polls of the full object.** -/
theorem F_use (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {x : Fin nk × Nat}
    (hx : x ∈ R.SF) (b : Fin nc) : x.2 ≤ okPolls R.F (X.tr (R.cons b)) := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  have hpres := Unit.present_of_path (R.reachF hX hx b (j := x.2 - 1) (by omega))
  have := Poll.nth_present.mp hpres
  omega

/-- **A notification's use is below every producer's polls of the empty object.** -/
theorem E_use (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) {y : Fin nc × Nat}
    (hy : y ∈ R.SE) (a : Fin np) : y.2 + 1 ≤ okPolls R.E (X.tr (R.prod a)) := by
  obtain ⟨i, -, hi, hp⟩ := R.polE y hy
  have hlt : y.2 < okPolls R.F (X.tr (R.cons y.1)) := by
    have := Poll.okPolls_mono R.F (X.tr (R.cons y.1)) hi.le
    rw [List.take_of_length_le le_rfl] at this
    omega
  obtain ⟨k, hk⟩ := R.cover a
  obtain ⟨j, -, hj, hpj⟩ := R.polF _ (R.full_observes hX hlt k).1
  simp only [hk] at hj hpj
  have := Poll.okPolls_mono R.E (X.tr (R.prod a)) hj.le
  rw [List.take_of_length_le le_rfl] at this
  omega

/-- **The final phase of the empty object** is at most a producer's polls. -/
theorem E_phase_le (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) (hnc : 0 < nc)
    (hinit : PairTmaRing.InitFirst X R.E nc)
    (hinc : ∀ r ∈ X.objects R.E, r.action ≠ .increment)
    (hone : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.E)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → c = 1)
    (hrec : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.E)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → ∃ y ∈ R.SE, r.id = R.note y.1 y.2)
    (a : Fin np) {st : State}
    (hst : stateBefore (X.objects R.E) (X.objects R.E).length = some st) :
    st.phase ≤ okPolls R.E (X.tr (R.prod a)) := by
  obtain ⟨h1, h2⟩ := units_bounds hX hinit R.cE.noInval hinc hone hrec hst
  have h3 : R.SE.card ≤ nc * okPolls R.E (X.tr (R.prod a)) := by
    calc R.SE.card ≤ (Finset.univ ×ˢ Finset.range (okPolls R.E (X.tr (R.prod a))) :
            Finset (Fin nc × Nat)).card := Finset.card_le_card fun y hy =>
          Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (R.E_use hX hy a)⟩
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_left (h2.trans (h1.trans h3)) hnc

/-- **At a blocked producer's poll the final phase of the empty object is one below its polls.** -/
theorem E_phase (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) (a : Fin np) {st : State}
    (hst : stateBefore (X.objects R.E) (X.objects R.E).length = some st)
    (hle : st.phase ≤ okPolls R.E (X.tr (R.prod a)))
    (hpar : st.phase % 2 = (okPolls R.E (X.tr (R.prod a)) + 1) % 2) :
    st.phase + 1 = okPolls R.E (X.tr (R.prod a)) := by
  have := okPolls_le_phase hX le_rfl (R.cE.pclean hX) R.cE.noInval
    (fun k pc q acq sc he => R.parE a he) hst
  omega

/-- **The final phase of the full object** is at most a consumer's polls plus one, when the arrivals
are those of the items of `N` kinds. -/
theorem F_phase_le (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk)
    {κ : Finset (Fin nk)} (hκ : 0 < κ.card) (hinit : PairTmaRing.InitFirst X R.F κ.card)
    (hinc : ∀ r ∈ X.objects R.F, r.action ≠ .increment)
    (hone : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.F)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → c = 1)
    (hrec : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects R.F)[k]? = some r → r.fault = none →
      r.action = .arrive c tx → ∃ x ∈ R.SF, x.1 ∈ κ ∧ r.id = R.itF x.1 x.2)
    (b : Fin nc) {st : State}
    (hst : stateBefore (X.objects R.F) (X.objects R.F).length = some st) :
    st.phase ≤ okPolls R.F (X.tr (R.cons b)) + 1 := by
  classical
  obtain ⟨h1, h2⟩ := units_bounds hX hinit R.cF.noInval hinc hone
    (S := R.SF.filter fun x => x.1 ∈ κ) (it := R.itF) (fun hr hf ha => by
      obtain ⟨x, hx, hk, hid⟩ := hrec hr hf ha
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, hk⟩, hid⟩) hst
  have h3 : (R.SF.filter fun x => x.1 ∈ κ).card ≤
      κ.card * (okPolls R.F (X.tr (R.cons b)) + 1) := by
    calc _ ≤ (κ ×ˢ Finset.range (okPolls R.F (X.tr (R.cons b)) + 1) :
            Finset (Fin nk × Nat)).card := Finset.card_le_card fun y hy => by
          obtain ⟨hy, hk⟩ := Finset.mem_filter.mp hy
          exact Finset.mem_product.mpr ⟨hk, Finset.mem_range.mpr
            (Nat.lt_succ_of_le (R.F_use hX hy b))⟩
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_left (h2.trans (h1.trans h3)) hκ

/-- **At a blocked consumer's poll the final phase of the full object is its polls.** -/
theorem F_phase (hX : Consistent L K A mem0 X) (R : KRing L K X np nc nk) (b : Fin nc) {st : State}
    (hst : stateBefore (X.objects R.F) (X.objects R.F).length = some st)
    (hle : st.phase ≤ okPolls R.F (X.tr (R.cons b)) + 1)
    (hpar : st.phase % 2 = okPolls R.F (X.tr (R.cons b)) % 2) :
    st.phase = okPolls R.F (X.tr (R.cons b)) := by
  have := okPolls_le_phase hX (Nat.zero_le 1) (R.cF.pclean hX) R.cF.noInval
    (fun k pc q acq sc he => R.parF b he) hst
  omega

end KRing
end
end PTX.MbarRing
