-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaUnits
public import Lemmas.Protocol.KindRingBlock
public import Lemmas.Protocol.TmaUnitBlock
public import Lemmas.Protocol.UnitObjBlocker

@[expose] public section

/-! # The producer of a TMA-fed full barrier at a blocked poll

A proof tool. When no tensor copy of the execution is open and no record of the barrier faults, the
thread that feeds a `TmaUnits.Obj` is short of the final phase's arrival or of one of its copies
(`Obj.short`), provided no counted item's use is beyond the phase. -/

namespace PTX.MbarRing.TmaUnits.Obj

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {y n bytes : Nat}

theorem one (o : Obj X m y n bytes) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (_hf : r.fault = none) (ha : r.action = .arrive c tx) :
    c = 1 := (o.arrive hr ha).1

/-- An arrival record is the counted item of kind 0. -/
theorem rec_zero (o : Obj X m y n bytes) (hn : 0 < n) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (hf : r.fault = none) (ha : r.action = .arrive c tx) :
    ∃ x ∈ S X m y n bytes, x.1 ∈ ({0} : Finset (Fin (n + 1))) ∧ r.id = it X m y n x.1 x.2 := by
  obtain ⟨x, hx, hid⟩ := o.item hr hf (.inl ⟨c, tx, ha⟩) hn
  refine ⟨x, hx, ?_, hid⟩
  by_contra hne
  have hz : x.1.val ≠ 0 := fun h => hne (Finset.mem_singleton.mpr (Fin.ext h))
  obtain ⟨-, -, j, pc, rel, sc, hj, -⟩ := o.arrive hr ha
  rw [hj] at hid
  simp only [it, hz, ↓reduceIte] at hid
  cases hid

private theorem expected (xs : List (Record Ref)) (T : Nat)
    (h : ∀ r ∈ xs, ∀ c tx, r.fault = none → r.action = .arrive c tx → c = 1 ∧ tx = T) :
    expectedTxBytes xs = T * arrivalUnits xs := by
  induction xs with
  | nil => simp [expectedTxBytes, arrivalUnits]
  | cons r rest ih =>
    have ih := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have h0 := h r List.mem_cons_self
    rw [expectedTxBytes, arrivalUnits, ih, Nat.mul_add]
    congr 1
    unfold Record.expectedTxBytes
    cases ha : r.action <;> cases hf : r.fault <;> simp
    obtain ⟨rfl, rfl⟩ := h0 _ _ hf ha
    simp

/-- **The feeding thread is short** of the final phase's arrival or of one of its copies. -/
theorem short (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hn : 0 < n)
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hno : ¬ Descent.Obl L X .tensor)
    {st : State} (hst : stateBefore (X.objects m) (X.objects m).length = some st)
    (huse : ∀ x ∈ S X m y n bytes, x.2 ≤ st.phase) :
    arrivals m (X.tr y) ≤ st.phase ∨
      (X.tr y).countP (issuesTo m) < n * (st.phase + 1) := by
  classical
  have hch := X.objects_checked hX m
  -- the completions are items of uses up to the phase
  have hle : completedTxCount (X.objects m) ≤ n * (st.phase + 1) := by
    unfold completedTxCount
    rw [← List.take_length (l := X.objects m), MbarRing.Slot.countP_take_card]
    calc _ ≤ ((Finset.univ.erase (0 : Fin (n + 1))) ×ˢ Finset.range (st.phase + 1)).card :=
          PairTmaRing.card_le_of_rel _ _
            (fun k x => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m y n x.1 x.2)
            (fun k hk => ?_) (fun k _ k' _ x _ h1 h2 => by
              obtain ⟨r, hr, hid⟩ := h1
              obtain ⟨r', hr', hid'⟩ := h2
              exact ObjectInit.checked_record_index_eq hch hr hr' (hid.trans hid'.symm))
      _ = _ := by simp
    obtain ⟨-, hk'⟩ := Finset.mem_filter.mp hk
    cases hr : (X.objects m)[k]? with
    | none => rw [hr] at hk'; simp at hk'
    | some r =>
      rw [hr, Option.any_some] at hk'
      split at hk'
      · rename_i b ha hf
        obtain ⟨x, hx, hid⟩ := o.item hr hf (.inr ⟨_, ha⟩) hn
        refine ⟨x, Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩,
          Finset.mem_range.mpr (Nat.lt_succ_of_le (huse x hx))⟩, r, rfl, hid⟩
        intro h0
        obtain ⟨-, j, pc, al, sp, hj, -⟩ := o.copy hr ha
        rw [hj] at hid
        simp [it, h0] at hid
      · cases hk'
  rcases Blocker.tx_short hch o.noInval hst (PairTmaRing.expected_of_init hX o.init o.noInval hst)
    (n := n) (B := bytes) (expected _ _ fun r hr c tx _ ha => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨h1, h2, -⟩ := o.arrive hk ha
      exact ⟨h1, h2⟩)
    (fun r hr _ b ha => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      exact (o.copy hk ha).1) hle o.noInc with h | ⟨-, h⟩
  · refine .inl (le_trans (Unit.arrivals_le_unitRec hX hff y) (le_trans ?_ h.le))
    have := Unit.sum_count_le_units (N := 1) (prod := fun _ => y)
      (fun a b _ => Subsingleton.elim a b) (X.objects m) fun r hr _ c tx ha => by
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
        exact (o.arrive hk ha).1
    simpa using this
  · refine .inr (lt_of_le_of_lt ?_ h)
    unfold completedTxCount
    refine countP_le_of_records (fun k => Ref.async (y, k) (Part.notify .load))
      (fun i j _ _ hf => by simpa using hf) (fun i hi => ?_)
    obtain ⟨⟨pc, kind⟩, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
    cases kind with
    | tensorIssue ma s =>
      have hmb : s.mbar = m := by simpa [Flow.issuesTo] using hp
      obtain ⟨r, hr, hid⟩ := TmaUnitObject.notified_rec hX hno (y, i) ma s ⟨pc, he⟩ hmb
      have hact := ((hX.tma.2.2.1 m).2.1 r hr).1
      rw [hid] at hact
      obtain ⟨b, hb⟩ := PairTmaRing.action_completeTx hact
      refine ⟨r, hr, hid, ?_⟩
      rw [hb, hff r hr]
    | _ => simp [Flow.issuesTo] at hp

end
end PTX.MbarRing.TmaUnits.Obj
