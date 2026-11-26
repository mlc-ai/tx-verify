-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaUnits

@[expose] public section

/-! # The counted items of a full barrier fed by TMA copies of several sizes

A proof tool, the generalization of `TmaUnits` (`Lemmas/Protocol/TmaUnits.lean`) to copies that
do not all move the same number of bytes. A full barrier of arrival count 1 whose updates are one
thread's: per use, one arrival expecting `U · W` bytes and the completions of `n` tensor copies,
the copy at position `i` of a use moving `U · wt cp i` bytes.

`TmaUnits` counts copies: a phase a poll observes holds one arrival and `n` completions, because
the bytes of the phase cancel and all copies have one size. With several sizes the number of
copies of a phase does not follow from its bytes. Here the bytes are counted in *units* of `U`
bytes (a common divisor of the sizes). There are `W` units per use; unit `u : Fin W` belongs to
the copy at position `cp u`, so position `i` has `wt cp i` units. A use has `W + 1` kinds of
item: kind `0` is the arrival with `t` earlier ones, kind `u + 1` is the copy that unit `u`
belongs to, the copy with `n t + cp u` earlier ones (`it`). Several kinds may name one copy; the
attribution engine (`MbarRing.Items.Ring`, `MbarRing.KRing`) never asks that kinds have different
records, so it is used unchanged.

* `Obj`: the description of the barrier's history (the analog of `TmaUnits.Obj`).
* `S`, `it`, `op`: the counted items, their records and their issues; `Obj.counted`,
  `Obj.source`, `Obj.issue`.
* `Obj.arrive_item`, `Obj.copy_items`: a fault-free arrival record is the item of kind `0` of
  its use; a fault-free completion record is the item of every kind that stands for its copy.
* `itemsAt k`: the counted items whose record is at position `k` of the history; they are
  disjoint for different positions (`itemsAt_disjoint`), and position `k` has at least as many
  as its arrival units plus its completed bytes divided by `U` (`Obj.units_le`).
* `Obj.card_phase`: **the phase a poll observes holds `W + 1` counted items.** The bytes of the
  phase cancel (`CheckedLog.completion_sums`), so its completions move `U · W` bytes, which are
  `W` units, each an item; and the phase has an arrival. -/

namespace PTX.MbarRing.TmaSized

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {y n W U : Nat} {cp : Fin W → Nat}

/-- The weight of position `i`: the number of units that belong to the copy at position `i` of
a use. -/
def wt (cp : Fin W → Nat) (i : Nat) : Nat := (Finset.univ.filter fun u : Fin W => cp u = i).card

theorem wt_le (cp : Fin W → Nat) (i : Nat) : wt cp i ≤ W := by
  have := Finset.card_le_univ (Finset.univ.filter fun u : Fin W => cp u = i)
  simpa [wt] using this

/-- **A full barrier whose updates are thread `y`'s**: arrivals of count 1 expecting `U · W`
bytes, and completions of tensor copies, the copy with `q` earlier ones on the barrier moving
`U · wt cp (q % n)` bytes. -/
structure Obj (X : Execution) (m : Loc) (y n U : Nat) (cp : Fin W → Nat) : Prop where
  init : PairTmaRing.InitFirst X m 1
  noInval : NoInval (X.objects m)
  incr : ∀ r ∈ X.objects m, r.action ≠ .increment
  arrive : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects m)[k]? = some r → r.action = .arrive c tx →
    c = 1 ∧ tx = U * W ∧ ∃ j pc rel sc, r.id = .thread (y, j) ∧
      X.get (y, j) = some ⟨pc, .arrive m tx 1 rel sc⟩
  copy : ∀ {k b : Nat} {r : Record Ref}, (X.objects m)[k]? = some r → r.action = .completeTx b →
    ∃ j pc al sp, r.id = .async (y, j) (.notify .load) ∧
      X.get (y, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = m ∧
      b = U * wt cp (((X.tr y).take j).countP (issuesTo m) % n)

/-- The position, among the copies of a use, of the copy that kind `k` stands for (`0` for the
arrival, where it is not used). -/
def pos (cp : Fin W → Nat) (k : Fin (W + 1)) : Nat := Fin.cases (motive := fun _ => Nat) 0 cp k

@[simp] theorem pos_succ (cp : Fin W → Nat) (u : Fin W) : pos cp u.succ = cp u := by simp [pos]

/-- The issue of an item. -/
def op (X : Execution) (m : Loc) (y n : Nat) (cp : Fin W → Nat) (k : Fin (W + 1)) (t : Nat) :
    EvId :=
  (y, if k = 0 then nthEv X (arrivesOn m) y t else nthEv X (issuesTo m) y (n * t + pos cp k))

/-- The item. -/
def it (X : Execution) (m : Loc) (y n : Nat) (cp : Fin W → Nat) (k : Fin (W + 1)) (t : Nat) :
    Ref :=
  if k = 0 then .thread (op X m y n cp k t) else .async (op X m y n cp k t) (.notify .load)

theorem it_zero (t : Nat) :
    it X m y n cp 0 t = .thread (y, nthEv X (arrivesOn m) y t) := by simp [it, op]

theorem it_succ (u : Fin W) (t : Nat) :
    it X m y n cp u.succ t =
      .async (y, nthEv X (issuesTo m) y (n * t + cp u)) (.notify .load) := by
  simp [it, op, Fin.succ_ne_zero]

open Classical in
/-- The counted items: those with a fault-free record. -/
def S (X : Execution) (m : Loc) (y n U : Nat) (cp : Fin W → Nat) : Finset (Fin (W + 1) × Nat) :=
  (Finset.univ ×ˢ Finset.range (X.tr y).length).filter fun x =>
    ∃ r ∈ X.objects m, r.id = it X m y n cp x.1 x.2 ∧ r.fault = none ∧
      (x.1 = 0 → r.action = .arrive 1 (U * W)) ∧ (x.1 ≠ 0 → ∃ b, r.action = .completeTx b)

/-- The kinds that stand for the copy at position `i`, as items of use `t`. -/
def unitItems (cp : Fin W → Nat) (i t : Nat) : Finset (Fin (W + 1) × Nat) :=
  (Finset.univ.filter fun u : Fin W => cp u = i).image fun u => (u.succ, t)

theorem card_unitItems (cp : Fin W → Nat) (i t : Nat) : (unitItems cp i t).card = wt cp i := by
  unfold unitItems wt
  exact Finset.card_image_of_injective _ fun a b h => Fin.succ_injective _ (Prod.mk.inj h).1

open Classical in
/-- The counted items whose record is at position `k` of the history. -/
def itemsAt (X : Execution) (m : Loc) (y n U : Nat) (cp : Fin W → Nat) (k : Nat) :
    Finset (Fin (W + 1) × Nat) :=
  (S X m y n U cp).filter fun x =>
    ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m y n cp x.1 x.2

/-- The completed bytes of the record at position `k`. -/
def cbAt (log : List (Record Ref)) (k : Nat) : Nat :=
  match log[k]? with
  | some r => r.completedTxBytes
  | none => 0

/-- Different positions have different items. -/
theorem itemsAt_disjoint (hX : Consistent L K A mem0 X) {k k' : Nat} (h : k ≠ k') :
    Disjoint (itemsAt X m y n U cp k) (itemsAt X m y n U cp k') := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨-, r, hr, hid⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, r', hr', hid'⟩ := Finset.mem_filter.mp hx'
  exact h (ObjectInit.checked_record_index_eq (X.objects_checked hX m) hr hr'
    (hid.trans hid'.symm))

/-- The record at position `k` of an item of that position. -/
theorem itemsAt_rec (hX : Consistent L K A mem0 X) {k : Nat} {x : Fin (W + 1) × Nat}
    (hx : x ∈ itemsAt X m y n U cp k) :
    ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m y n cp x.1 x.2 ∧ r.fault = none ∧
      (x.1 = 0 → r.action = .arrive 1 (U * W)) ∧ (x.1 ≠ 0 → ∃ b, r.action = .completeTx b) := by
  classical
  obtain ⟨hxS, r, hr, hid⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, r', hr', hid', hf, h0, h1⟩ := Finset.mem_filter.mp hxS
  have := hX.record_eq hr' (List.mem_of_getElem? hr) (hid'.trans hid.symm)
  subst this
  exact ⟨r', hr, hid, hf, h0, h1⟩

namespace Obj

/-- A counted item's record and issue. -/
theorem source (o : Obj X m y n U cp) {x : Fin (W + 1) × Nat} (hx : x ∈ S X m y n U cp) :
    (∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it X m y n cp x.1 x.2 ∧
      r.fault = none ∧ CounterUpdate r.action) ∧
    (x.1 = 0 → (∃ pc rel sc, X.get (op X m y n cp x.1 x.2) =
        some ⟨pc, .arrive m (U * W) 1 rel sc⟩) ∧
      arrivals m ((X.tr y).take (op X m y n cp x.1 x.2).2) = x.2) ∧
    (x.1 ≠ 0 → (∃ pc al sp, X.get (op X m y n cp x.1 x.2) = some ⟨pc, .tensorIssue al sp⟩ ∧
        sp.mbar = m) ∧
      ((X.tr y).take (op X m y n cp x.1 x.2).2).countP (issuesTo m) = n * x.2 + pos cp x.1) := by
  classical
  obtain ⟨-, r, hr, hid, hf, h0, h1⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  by_cases hz : x.1 = 0
  · obtain ⟨-, -, j, pc, rel, sc, hj, he⟩ := o.arrive hk (h0 hz)
    have hji : (y, j) = op X m y n cp x.1 x.2 := by
      rw [hid] at hj
      simp only [it, hz, ↓reduceIte, Ref.thread.injEq] at hj
      rw [hz]
      exact hj.symm
    have hj2 : j = nthEv X (arrivesOn m) y x.2 := by
      have := congrArg Prod.snd hji
      simpa [op, hz] using this
    refine ⟨⟨k, r, hk, hid, hf, by rw [h0 hz]; trivial⟩, fun _ => ⟨⟨pc, rel, sc, hji ▸ he⟩, ?_⟩,
      fun h => absurd hz h⟩
    rw [← hji]
    unfold arrivals
    exact (by rw [hj2]; exact (nthEv_spec_of_get (hj2 ▸ he)).2)
  · obtain ⟨b, hb⟩ := h1 hz
    obtain ⟨j, pc, al, sp, hj, he, hm, -⟩ := o.copy hk hb
    have hji : (y, j) = op X m y n cp x.1 x.2 := by
      rw [hid] at hj
      simp only [it, hz, ↓reduceIte, Ref.async.injEq, and_true] at hj
      exact hj.symm
    have hj2 : j = nthEv X (issuesTo m) y (n * x.2 + pos cp x.1) := by
      have := congrArg Prod.snd hji
      simpa [op, hz] using this
    refine ⟨⟨k, r, hk, hid, hf, by rw [hb]; trivial⟩, fun h => absurd h hz,
      fun _ => ⟨⟨pc, al, sp, hji ▸ he, hm⟩, ?_⟩⟩
    rw [← hji]
    exact (by rw [hj2]; exact (nthEv_spec_of_get (hj2 ▸ he)).2)

/-- **A fault-free arrival record is the counted item of kind `0` of its use.** -/
theorem arrive_item (o : Obj X m y n U cp) {k c tx : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (hf : r.fault = none) (ha : r.action = .arrive c tx) :
    ∃ t, ((0 : Fin (W + 1)), t) ∈ S X m y n U cp ∧ r.id = it X m y n cp 0 t := by
  classical
  obtain ⟨rfl, rfl, j, pc, rel, sc, hid, he⟩ := o.arrive hr ha
  have hp : arrivesOn m ⟨pc, .arrive m (U * W) 1 rel sc⟩ = true := by
    simp [arrivesOn, sourceArrive]
  have hlen := len_of_get he
  have hcj : ((X.tr y).take j).countP (arrivesOn m) ≤ j :=
    List.countP_le_length.trans (List.length_take_le _ _)
  have hlt : ((X.tr y).take j).countP (arrivesOn m) < (X.tr y).length := by
    simp only at hlen
    omega
  have hit : r.id = it X m y n cp 0 (((X.tr y).take j).countP (arrivesOn m)) := by
    rw [hid, it_zero, nthEv_eq he hp]
  exact ⟨((X.tr y).take j).countP (arrivesOn m), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hlt⟩, r,
      List.mem_of_getElem? hr, hit, hf, fun _ => ha, fun h => absurd rfl h⟩, hit⟩

/-- **A fault-free completion record is the counted item of every kind that stands for its
copy**: the copy with `q` earlier ones is at position `q % n` of use `q / n`. -/
theorem copy_items (o : Obj X m y n U cp) {k b : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) (hf : r.fault = none) (ha : r.action = .completeTx b) :
    ∃ q, b = U * wt cp (q % n) ∧ (∃ j pc al sp, r.id = .async (y, j) (.notify .load) ∧
        X.get (y, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = m ∧
        ((X.tr y).take j).countP (issuesTo m) = q) ∧
      ∀ u : Fin W, cp u = q % n →
        (u.succ, q / n) ∈ S X m y n U cp ∧ r.id = it X m y n cp u.succ (q / n) := by
  classical
  obtain ⟨j, pc, al, sp, hid, he, hm, hb⟩ := o.copy hr ha
  have hp : issuesTo m ⟨pc, .tensorIssue al sp⟩ = true := by simp [issuesTo, hm]
  have hlen := len_of_get he
  have hqj : ((X.tr y).take j).countP (issuesTo m) ≤ j :=
    List.countP_le_length.trans (List.length_take_le _ _)
  refine ⟨_, hb, ⟨j, pc, al, sp, hid, he, hm, rfl⟩, fun u hu => ?_⟩
  have hit : r.id = it X m y n cp u.succ (((X.tr y).take j).countP (issuesTo m) / n) := by
    rw [hid, it_succ, hu, Nat.div_add_mod, nthEv_eq he hp]
  have hdl := Nat.div_le_self (((X.tr y).take j).countP (issuesTo m)) n
  have hlt : ((X.tr y).take j).countP (issuesTo m) / n < (X.tr y).length := by
    simp only at hlen
    omega
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_range.mpr hlt⟩, r, List.mem_of_getElem? hr, hit, hf,
    fun h => absurd h (Fin.succ_ne_zero u), fun _ => ⟨b, ha⟩⟩, hit⟩

theorem counted (o : Obj X m y n U cp) : Counted X m (S X m y n U cp) (it X m y n cp) where
  record _ hx := (o.source hx).1
  init := ⟨1, o.init⟩
  noInval := o.noInval

/-- The issue of an item precedes it. -/
theorem issue (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) {x : Fin (W + 1) × Nat}
    (hx : x ∈ S X m y n U cp) :
    Relation.ReflTransGen (DepStep L K X) (.thread (op X m y n cp x.1 x.2), false)
      (it X m y n cp x.1 x.2, false) := by
  obtain ⟨⟨i, r, hi, hid, -⟩, -, h1⟩ := o.source hx
  by_cases hk : x.1 = 0
  · have h : it X m y n cp x.1 x.2 = .thread (op X m y n cp x.1 x.2) := by simp [it, hk]
    rw [h]
  · obtain ⟨⟨pc, al, sp, he, -⟩, -⟩ := h1 hk
    have h : it X m y n cp x.1 x.2 = .async (op X m y n cp x.1 x.2) (.notify .load) := by
      simp [it, hk]
    rw [h]
    have hp := object_record_present hX.tma (List.mem_of_getElem? hi)
    rw [hid, h] at hp
    obtain ⟨o', ho, hn⟩ := id hp
    obtain ⟨x', y', k', hwp⟩ := tensor_write_present hX.effectValidity ho hn
    exact (((Relation.TransGen.single (DepStep.issue (L := L) (K := K)
      (p := .write (.load x' y' k')) ⟨_, he⟩ hwp (fun _ h => by cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h))).tail (DepStep.node hwp)).tail (DepStep.stage
        (c := (.async (op X m y n cp x.1 x.2) (.notify .load), false))
        (.inr ⟨rfl, rfl, rfl, rfl, hwp, hp⟩))).to_reflTransGen

theorem noInc (o : Obj X m y n U cp) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => o.incr r hr hi

/-- The expected bytes of a record are `U · W` per arrival unit. -/
theorem expected_eq (o : Obj X m y n U cp) {k : Nat} {r : Record Ref}
    (hr : (X.objects m)[k]? = some r) :
    r.expectedTxBytes = U * W * (if r.fault = none then r.action.units else 0) := by
  unfold Record.expectedTxBytes
  cases ha : r.action with
  | arrive c tx =>
    obtain ⟨rfl, rfl, -⟩ := o.arrive hr ha
    cases r.fault <;> simp [Action.units]
  | _ => cases r.fault <;> simp [Action.units]

/-- The completed bytes of a position are a multiple of the unit. -/
theorem cb_dvd (o : Obj X m y n U cp) (k : Nat) : U ∣ cbAt (X.objects m) k := by
  unfold cbAt
  cases hr : (X.objects m)[k]? with
  | none => exact dvd_zero _
  | some r =>
    simp only
    unfold Record.completedTxBytes
    cases ha : r.action with
    | completeTx b =>
      obtain ⟨j, pc, al, sp, -, -, -, rfl⟩ := o.copy hr ha
      cases r.fault
      · exact Dvd.intro _ rfl
      · exact dvd_zero _
    | _ => cases r.fault <;> exact dvd_zero _

/-- A position has at least as many items of kind `0` as arrival units. -/
theorem arr_le (o : Obj X m y n U cp) (k : Nat) :
    unitsAt (X.objects m) k ≤
      ((itemsAt X m y n U cp k).filter fun x => x.1 = 0).card := by
  classical
  unfold unitsAt
  cases hr : (X.objects m)[k]? with
  | none => exact Nat.zero_le _
  | some r =>
    simp only
    by_cases hf : r.fault = none
    · rw [ite_eq_left hf]
      cases ha : r.action with
      | arrive c tx =>
        obtain ⟨t, hS, hid⟩ := o.arrive_item hr hf ha
        obtain ⟨rfl, -⟩ := o.arrive hr ha
        exact Finset.card_pos.mpr ⟨(0, t), Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hS, r, hr, hid⟩, rfl⟩⟩
      | _ => exact Nat.zero_le _
    · rw [ite_eq_right hf]
      exact Nat.zero_le _

/-- A position has at least as many items of the other kinds as completed units. -/
theorem cb_le (o : Obj X m y n U cp) (hU : 0 < U) (k : Nat) :
    cbAt (X.objects m) k / U ≤
      ((itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card := by
  classical
  unfold cbAt
  cases hr : (X.objects m)[k]? with
  | none => simp
  | some r =>
    simp only
    unfold Record.completedTxBytes
    cases ha : r.action with
    | completeTx b =>
      cases hf : r.fault with
      | some err => simp
      | none =>
        obtain ⟨q, rfl, -, hq⟩ := o.copy_items hr hf ha
        simp only
        rw [Nat.mul_div_cancel_left _ hU, ← card_unitItems cp (q % n) (q / n)]
        refine Finset.card_le_card fun x hx => ?_
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hS, hid⟩ := hq u (Finset.mem_filter.mp hu).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hS, r, hr, hid⟩,
          Fin.succ_ne_zero u⟩
    | _ => cases r.fault <;> simp

/-- **A position has at least as many items as its arrival units plus its completed units.** -/
theorem units_le (o : Obj X m y n U cp) (hU : 0 < U) (k : Nat) :
    unitsAt (X.objects m) k + cbAt (X.objects m) k / U ≤ (itemsAt X m y n U cp k).card := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := itemsAt X m y n U cp k)
    (p := fun x => x.1 = 0)]
  exact Nat.add_le_add (o.arr_le k) (o.cb_le hU k)

/-- The transaction effect of a position: its expected bytes less its completed bytes. -/
theorem txDeltaAt_eq (o : Obj X m y n U cp) (k : Nat) :
    txDeltaAt (X.objects m) k =
      ((U * W * unitsAt (X.objects m) k : Nat) : Int) - (cbAt (X.objects m) k : Nat) := by
  unfold txDeltaAt unitsAt cbAt
  cases hr : (X.objects m)[k]? with
  | none => simp
  | some r =>
    simp only
    rw [Record.txDelta_eq_bytes, o.expected_eq hr]

open Classical in
/-- **The phase a poll observes holds `W + 1` counted items**: an arrival, and the kinds of the
`W` units that the phase's completions move, since the phase's transaction updates cancel. -/
theorem card_phase (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hU : 0 < U)
    {g j δ : Nat} (hδ' : δ ≤ 1)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ) (hδ : δ ≤ j)
    (hj : j < okPolls m (X.tr g)) :
    W + 1 ≤ ((S X m y n U cp).filter
      (fun x => Counted.ph X m (it X m y n cp) x = Unit.obsOf X m g j)).card := by
  obtain ⟨iw, w, st, hiw, -, -, -, hst, hpos, -, hoF⟩ :=
    o.counted.poll_obs hX hδ' hAlt hδ hj
  obtain ⟨q, hq⟩ : ∃ q, st.phase = q + 1 := ⟨st.phase - 1, by omega⟩
  rw [hq, Nat.add_sub_cancel] at hoF
  have hch : CheckedLog (X.objects m) := X.objects_checked hX m
  have hni := o.noInval
  have hiwl : iw ≤ (X.objects m).length := (List.getElem?_eq_some_iff.mp hiw).1.le
  obtain ⟨e, he, hce⟩ := hch.crossing hni (c := q) hiwl hst (by omega)
  have hel : e < (X.objects m).length := by
    have := (List.getElem?_eq_some_iff.mp hiw).1
    omega
  obtain ⟨hsum, hunits⟩ := hch.completion_sums hni hel hce
  -- the positions of phase `q`
  let P := (Finset.range (e + 1)).filter fun k => phaseAt (X.objects m) k = some q
  have hTx : phaseTx (X.objects m) (e + 1) q = ∑ k ∈ P, txDeltaAt (X.objects m) k := by
    unfold phaseTx
    rw [Finset.sum_filter]
  have hUn : phaseUnits (X.objects m) (e + 1) q = ∑ k ∈ P, unitsAt (X.objects m) k := by
    unfold phaseUnits
    rw [Finset.sum_filter]
  -- the completed bytes of the phase are its expected bytes
  have hcb : ∑ k ∈ P, cbAt (X.objects m) k = U * W * ∑ k ∈ P, unitsAt (X.objects m) k := by
    have h0 : (0 : Int) = ∑ k ∈ P, (((U * W * unitsAt (X.objects m) k : Nat) : Int) -
        (cbAt (X.objects m) k : Nat)) := by
      rw [← hsum, hTx]
      exact Finset.sum_congr rfl fun k _ => o.txDeltaAt_eq k
    rw [Finset.sum_sub_distrib] at h0
    have h2 : ((∑ k ∈ P, cbAt (X.objects m) k : Nat) : Int) =
        ((U * W * ∑ k ∈ P, unitsAt (X.objects m) k : Nat) : Int) := by
      rw [Finset.mul_sum]
      push_cast at h0 ⊢
      linarith
    exact_mod_cast h2
  have hdiv : U * ∑ k ∈ P, cbAt (X.objects m) k / U = ∑ k ∈ P, cbAt (X.objects m) k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Nat.mul_div_cancel' (o.cb_dvd k)
  have h1 : 1 ≤ ∑ k ∈ P, unitsAt (X.objects m) k := by
    rw [← hUn]
    exact hunits
  have hW : W ≤ ∑ k ∈ P, cbAt (X.objects m) k / U := by
    have h : U * W ≤ U * ∑ k ∈ P, cbAt (X.objects m) k / U := by
      rw [hdiv, hcb]
      exact Nat.le_mul_of_pos_right _ (by omega)
    exact Nat.le_of_mul_le_mul_left h hU
  calc W + 1 ≤ ∑ k ∈ P, (unitsAt (X.objects m) k + cbAt (X.objects m) k / U) := by
        rw [Finset.sum_add_distrib]
        omega
    _ ≤ ∑ k ∈ P, (itemsAt X m y n U cp k).card :=
        Finset.sum_le_sum fun k _ => o.units_le hU k
    _ = (P.biUnion (itemsAt X m y n U cp)).card :=
        (Finset.card_biUnion fun k _ k' _ h => itemsAt_disjoint hX h).symm
    _ ≤ _ := Finset.card_le_card (Finset.biUnion_subset.mpr fun k hk x hx => by
        obtain ⟨hxS, r, hr, hid⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨hxS, ?_⟩
        unfold Counted.ph
        rw [← hid, MbarRing.Poll.phaseOf_eq hX hr (Finset.mem_filter.mp hk).2, hoF])

end Obj

end
end PTX.MbarRing.TmaSized
