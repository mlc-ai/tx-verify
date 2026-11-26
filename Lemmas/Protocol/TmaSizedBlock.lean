-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaSizedFault
public import Lemmas.Protocol.TmaUnitsBlock

@[expose] public section

/-! # The producer of a full barrier fed by TMA copies of several sizes, at a blocked poll

A proof tool for progress, the analog of `TmaUnitsBlock` (`Lemmas/Protocol/TmaUnitsBlock.lean`)
for the object of `TmaSized.Obj`. When no tensor copy of the execution is open and no record of
the barrier faults, the thread that feeds the barrier is short of the final phase's arrival or
of one of its copies (`Obj.short`), provided no counted item's use is beyond the phase and every
unit belongs to one of the `n` positions of a use.

The argument counts units. The history's completed bytes are `U` times its completed units
(`cb_sum_le`, `le_cb_sum`): at most `W` per use up to the final phase, and at least that many
once the thread has issued all copies of those uses and each has completed. With the phase's
arrival in, the two bounds would make the transaction counter zero, and a phase whose counter
is zero and whose arrival is in has advanced.

* `Obj.filter_card_le`: the converse of `Obj.cb_le`: the items of the copy kinds at a position
  are at most the position's completed units, when every unit's position is below `n`.
* `Obj.cb_sum_le`: the completed units of a history whose counted items have uses at most `N`
  are at most `W (N + 1)`.
* `Obj.le_cb_sum`: they are at least `W (N + 1)` when the feeding thread has issued
  `n (N + 1)` copies, no record faults and no tensor copy is open.
* `Obj.short`: the blocker. -/

namespace PTX.MbarRing.TmaSized.Obj

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {y n W U : Nat} {cp : Fin W → Nat}

/-- **The items of the copy kinds at a position are at most its completed units**, when every
unit's position is below `n`: an item of the position names the position's copy, so its kind is
one of the copy's units and its use is the copy's. -/
theorem filter_card_le (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hn : 0 < n)
    (hU : 0 < U) (hcp : ∀ u, cp u < n) (k : Nat) :
    ((itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card ≤ cbAt (X.objects m) k / U := by
  classical
  by_cases hne : ((itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨hx0I, hx00⟩ := Finset.mem_filter.mp hx0
  obtain ⟨r, hr, -, hf, -, h1⟩ := itemsAt_rec hX hx0I
  obtain ⟨b, ha⟩ := h1 hx00
  obtain ⟨q, hb, ⟨j, pc, al, sp, hidj, he, hm, hq⟩, -⟩ := o.copy_items hr hf ha
  have hcb : cbAt (X.objects m) k = b := by
    simp [cbAt, hr, Record.completedTxBytes, ha, hf]
  rw [hcb, hb, Nat.mul_div_cancel_left _ hU, ← card_unitItems cp (q % n) (q / n)]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨hxI, hx0'⟩ := Finset.mem_filter.mp hx
  obtain ⟨r', hr', hid, -⟩ := itemsAt_rec hX hxI
  rw [hr] at hr'
  cases hr'
  obtain ⟨u, hu⟩ := Fin.exists_succ_eq.mpr hx0'
  obtain ⟨-, -, h2⟩ := o.source (Finset.mem_filter.mp hxI).1
  obtain ⟨-, hcnt⟩ := h2 hx0'
  -- the item's issue is the record's copy
  have hop : op X m y n cp x.1 x.2 = (y, j) := by
    rw [hidj] at hid
    simp only [it, hx0', ↓reduceIte, Ref.async.injEq, and_true] at hid
    exact hid.symm
  have hqe : q = n * x.2 + cp u := by
    rw [hop] at hcnt
    rw [← hq, hcnt, ← hu, pos_succ]
  have hmod : q % n = cp u := by
    rw [hqe, Nat.mul_add_mod, Nat.mod_eq_of_lt (hcp u)]
  have hdiv : q / n = x.2 := by
    rw [hqe, Nat.mul_add_div hn, Nat.div_eq_of_lt (hcp u), Nat.add_zero]
  refine Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmod.symm⟩, ?_⟩
  exact Prod.ext hu hdiv

/-- The completed bytes of a history are `U` times its completed units. -/
theorem cb_sum (o : Obj X m y n U cp) :
    completedTxBytes (X.objects m) =
      U * ∑ k ∈ Finset.range (X.objects m).length, cbAt (X.objects m) k / U := by
  rw [completedTxBytes_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => (Nat.mul_div_cancel' (o.cb_dvd k)).symm

/-- **The completed units of a history whose counted items have uses at most `N`** are at most
`W` per use. -/
theorem cb_sum_le (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hU : 0 < U) {N : Nat}
    (huse : ∀ x ∈ S X m y n U cp, x.2 ≤ N) :
    ∑ k ∈ Finset.range (X.objects m).length, cbAt (X.objects m) k / U ≤ W * (N + 1) := by
  classical
  have hT : ((Finset.univ.erase (0 : Fin (W + 1))) ×ˢ Finset.range (N + 1)).card =
      W * (N + 1) := by simp
  rw [← hT]
  calc ∑ k ∈ Finset.range (X.objects m).length, cbAt (X.objects m) k / U
      ≤ ∑ k ∈ Finset.range (X.objects m).length,
          ((itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card :=
        Finset.sum_le_sum fun k _ => o.cb_le hU k
    _ = ((Finset.range (X.objects m).length).biUnion fun k =>
          (itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card :=
        (Finset.card_biUnion fun k _ k' _ h =>
          Finset.disjoint_filter_filter (itemsAt_disjoint hX h)).symm
    _ ≤ _ := Finset.card_le_card (Finset.biUnion_subset.mpr fun k _ x hx => by
        obtain ⟨hxI, hx0⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ _⟩,
          Finset.mem_range.mpr (Nat.lt_succ_of_le (huse x (Finset.mem_filter.mp hxI).1))⟩)

/-- **The completed units of a history are at least `W` per use issued in full**, when no
record faults and every issued copy has completed. -/
theorem le_cb_sum (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hn : 0 < n)
    (hU : 0 < U) (hcp : ∀ u, cp u < n) (hff : ∀ r ∈ X.objects m, r.fault = none)
    (hno : ¬ Descent.Obl L X .tensor) {N : Nat}
    (hiss : n * (N + 1) ≤ (X.tr y).countP (issuesTo m)) :
    W * (N + 1) ≤ ∑ k ∈ Finset.range (X.objects m).length, cbAt (X.objects m) k / U := by
  classical
  have hT : ((Finset.univ.erase (0 : Fin (W + 1))) ×ˢ Finset.range (N + 1)).card =
      W * (N + 1) := by simp
  rw [← hT]
  calc ((Finset.univ.erase (0 : Fin (W + 1))) ×ˢ Finset.range (N + 1)).card
      ≤ ((Finset.range (X.objects m).length).biUnion fun k =>
          (itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card :=
        Finset.card_le_card fun x hx => ?_
    _ ≤ ∑ k ∈ Finset.range (X.objects m).length,
          ((itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun k _ => o.filter_card_le hX hn hU hcp k
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
  have hx0 : x.1 ≠ 0 := (Finset.mem_erase.mp h1).1
  have hxN : x.2 ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp h2)
  obtain ⟨u, hu⟩ := Fin.exists_succ_eq.mpr hx0
  -- the copy of this kind and use is issued
  have hq : n * x.2 + cp u < (X.tr y).countP (issuesTo m) := by
    have h3 := hcp u
    have h4 : n * x.2 + n ≤ n * (N + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left n hxN) n
    omega
  obtain ⟨⟨pc, kind⟩, he, hp, hc⟩ := nthEv_spec hq
  cases kind with
  | tensorIssue ma s =>
    have hmb : s.mbar = m := by simpa [Flow.issuesTo] using hp
    -- and has completed
    obtain ⟨r, hr, hid⟩ := TmaUnitObject.notified_rec hX hno (y, _) ma s ⟨pc, he⟩ hmb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    have hact := ((hX.tma.2.2.1 m).2.1 r hr).1
    rw [hid] at hact
    obtain ⟨b, hb⟩ := PairTmaRing.action_completeTx hact
    have hit : r.id = it X m y n cp x.1 x.2 := by rw [hid, ← hu, it_succ]
    have hlen : x.2 < (X.tr y).length := by
      have h5 := len_of_get he
      have h6 : ((X.tr y).take (nthEv X (issuesTo m) y (n * x.2 + cp u))).countP (issuesTo m) ≤
          nthEv X (issuesTo m) y (n * x.2 + cp u) :=
        List.countP_le_length.trans (List.length_take_le _ _)
      have h7 : x.2 ≤ n * x.2 := Nat.le_mul_of_pos_left _ hn
      simp only at h5
      omega
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hk).1,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hlen⟩, r, hr, hit,
          hff r hr, fun h => absurd h hx0, fun _ => ⟨b, hb⟩⟩, r, hk, hit⟩, hx0⟩⟩
  | _ => simp [Flow.issuesTo] at hp

/-- **The feeding thread is short** of the final phase's arrival or of one of its copies. -/
theorem short (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hn : 0 < n) (hU : 0 < U)
    (hcp : ∀ u, cp u < n) (hff : ∀ r ∈ X.objects m, r.fault = none)
    (hno : ¬ Descent.Obl L X .tensor) {st : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some st)
    (huse : ∀ x ∈ S X m y n U cp, x.2 ≤ st.phase) :
    arrivals m (X.tr y) ≤ st.phase ∨
      (X.tr y).countP (issuesTo m) < n * (st.phase + 1) := by
  classical
  have hch := X.objects_checked hX m
  have hni := o.noInval
  have hexp := PairTmaRing.expected_of_init hX o.init o.noInval hst
  obtain ⟨hpend, hacc⟩ := (hch.accounted hni le_rfl).2 st hst
  simp only [unitsBefore, List.take_length] at hacc
  rw [hexp, o.noInc] at hpend hacc
  rcases (show st.pending = 0 ∨ st.pending = 1 by omega) with hp0 | hp1
  · -- the phase's arrival is in: a copy is missing
    refine .inr ?_
    by_contra hge
    have hlo := o.le_cb_sum hX hn hU hcp hff hno (Nat.le_of_not_lt hge)
    have hhi := o.cb_sum_le hX hU huse
    have hcomp : completedTxBytes (X.objects m) = U * W * (st.phase + 1) := by
      rw [o.cb_sum, Nat.le_antisymm hhi hlo, Nat.mul_assoc]
    have hbal := hch.tx_balance hni le_rfl hst
    rw [List.take_length, o.expected_bytes _ (fun r hr => hr), hcomp,
      show arrivalUnits (X.objects m) = st.phase + 1 by omega] at hbal
    have htx : st.tx = 0 := by rw [hbal]; simp
    have := stateBefore_pending_pos hch hst htx
    omega
  · -- the phase's arrival is missing
    refine .inl (le_trans (Unit.arrivals_le_unitRec hX hff y)
      (le_trans ?_ (show arrivalUnits (X.objects m) ≤ st.phase by omega)))
    have := Unit.sum_count_le_units (N := 1) (prod := fun _ => y)
      (fun a b _ => Subsingleton.elim a b) (X.objects m) fun r hr _ c tx ha => by
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
        exact (o.arrive hk ha).1
    simpa using this

end
end PTX.MbarRing.TmaSized.Obj
