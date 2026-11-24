-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.KindRing
public import Lemmas.Protocol.SingleTmaRing.Attribution
public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # The counted items of a full barrier fed by TMA copies

A proof tool. A full barrier of arrival count 1 whose updates are one thread's: an arrival expecting
`n · bytes` bytes and the completions of tensor copies of `bytes` bytes. Kind `0` is the arrival
with `t` earlier ones; kind `i + 1` the copy with `n t + i` earlier ones (`it`). Every phase a poll
observes holds `n + 1` of them (`Obj.card_phase`). -/

namespace PTX.MbarRing.TmaUnits

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {y n bytes : Nat}

/-- **A full barrier whose updates are thread `y`'s**. -/
structure Obj (X : Execution) (m : Loc) (y n bytes : Nat) : Prop where
  init : PairTmaRing.InitFirst X m 1
  noInval : NoInval (X.objects m)
  incr : ∀ r ∈ X.objects m, r.action ≠ .increment
  arrive : ∀ {k c tx : Nat} {r : Record Ref}, (X.objects m)[k]? = some r → r.action = .arrive c tx →
    c = 1 ∧ tx = n * bytes ∧ ∃ j pc rel sc, r.id = .thread (y, j) ∧
      X.get (y, j) = some ⟨pc, .arrive m tx 1 rel sc⟩
  copy : ∀ {k b : Nat} {r : Record Ref}, (X.objects m)[k]? = some r → r.action = .completeTx b →
    b = bytes ∧ ∃ j pc al sp, r.id = .async (y, j) (.notify .load) ∧
      X.get (y, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = m

/-- The issue of an item. -/
def op (X : Execution) (m : Loc) (y n : Nat) (k : Fin (n + 1)) (t : Nat) : EvId :=
  (y, if k.val = 0 then nthEv X (arrivesOn m) y t else nthEv X (issuesTo m) y (n * t + (k.val - 1)))

/-- The item. -/
def it (X : Execution) (m : Loc) (y n : Nat) (k : Fin (n + 1)) (t : Nat) : Ref :=
  if k.val = 0 then .thread (op X m y n k t) else .async (op X m y n k t) (.notify .load)

open Classical in
/-- The counted items: those with a fault-free record. -/
def S (X : Execution) (m : Loc) (y n bytes : Nat) : Finset (Fin (n + 1) × Nat) :=
  (Finset.univ ×ˢ Finset.range (X.tr y).length).filter fun x =>
    ∃ r ∈ X.objects m, r.id = it X m y n x.1 x.2 ∧ r.fault = none ∧
      (x.1.val = 0 → r.action = .arrive 1 (n * bytes)) ∧
      (x.1.val ≠ 0 → r.action = .completeTx bytes)

namespace Obj

/-- A counted item's record and issue. -/
theorem source (o : Obj X m y n bytes) {x : Fin (n + 1) × Nat} (hx : x ∈ S X m y n bytes) :
    (∃ (k : Nat) (r : Record Ref), (X.objects m)[k]? = some r ∧ r.id = it X m y n x.1 x.2 ∧
      r.fault = none ∧ CounterUpdate r.action) ∧
    (x.1.val = 0 → (∃ pc rel sc, X.get (op X m y n x.1 x.2) =
        some ⟨pc, .arrive m (n * bytes) 1 rel sc⟩) ∧
      arrivals m ((X.tr y).take (op X m y n x.1 x.2).2) = x.2) ∧
    (x.1.val ≠ 0 → (∃ pc al sp, X.get (op X m y n x.1 x.2) = some ⟨pc, .tensorIssue al sp⟩ ∧
        sp.mbar = m) ∧
      ((X.tr y).take (op X m y n x.1 x.2).2).countP (issuesTo m) = n * x.2 + (x.1.val - 1)) := by
  obtain ⟨-, r, hr, hid, hf, h0, h1⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  by_cases hz : x.1.val = 0
  · obtain ⟨-, -, j, pc, rel, sc, hj, he⟩ := o.arrive hk (h0 hz)
    have hji : (y, j) = op X m y n x.1 x.2 := by
      rw [hid] at hj
      simp only [it, hz, ↓reduceIte, Ref.thread.injEq] at hj
      exact hj.symm
    have hj2 : j = nthEv X (arrivesOn m) y x.2 := by
      have := congrArg Prod.snd hji
      simpa [op, hz] using this
    refine ⟨⟨k, r, hk, hid, hf, by rw [h0 hz]; trivial⟩, fun _ => ⟨⟨pc, rel, sc, hji ▸ he⟩, ?_⟩,
      fun h => absurd hz h⟩
    have hp : arrivesOn m ⟨pc, .arrive m (n * bytes) 1 rel sc⟩ = true := by
      simp [arrivesOn, sourceArrive]
    rw [← hji]
    unfold arrivals
    exact (by rw [hj2]; exact (nthEv_spec_of_get (hj2 ▸ he)).2)
  · obtain ⟨-, j, pc, al, sp, hj, he, hm⟩ := o.copy hk (h1 hz)
    have hji : (y, j) = op X m y n x.1 x.2 := by
      rw [hid] at hj
      simp only [it, hz, ↓reduceIte, Ref.async.injEq, and_true] at hj
      exact hj.symm
    have hj2 : j = nthEv X (issuesTo m) y (n * x.2 + (x.1.val - 1)) := by
      have := congrArg Prod.snd hji
      simpa [op, hz] using this
    refine ⟨⟨k, r, hk, hid, hf, by rw [h1 hz]; trivial⟩, fun h => absurd h hz,
      fun _ => ⟨⟨pc, al, sp, hji ▸ he, hm⟩, ?_⟩⟩
    rw [← hji]
    exact (by rw [hj2]; exact (nthEv_spec_of_get (hj2 ▸ he)).2)

/-- A fault-free update is a counted item's. -/
theorem item (o : Obj X m y n bytes) {k : Nat} {r : Record Ref} (hr : (X.objects m)[k]? = some r)
    (hf : r.fault = none)
    (hu : (∃ c tx, r.action = .arrive c tx) ∨ ∃ b, r.action = .completeTx b) (hn : 0 < n) :
    ∃ x ∈ S X m y n bytes, r.id = it X m y n x.1 x.2 := by
  classical
  have hmem : ∀ x : Fin (n + 1) × Nat, x.2 < (X.tr y).length → r.id = it X m y n x.1 x.2 →
      (x.1.val = 0 → r.action = .arrive 1 (n * bytes)) →
      (x.1.val ≠ 0 → r.action = .completeTx bytes) →
      ∃ x ∈ S X m y n bytes, r.id = it X m y n x.1 x.2 := fun x hl hid h0 h1 =>
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_range.mpr hl⟩, r, List.mem_of_getElem? hr, hid, hf, h0, h1⟩, hid⟩
  rcases hu with ⟨c, tx, ha⟩ | ⟨b, ha⟩
  · obtain ⟨rfl, rfl, j, pc, rel, sc, hid, he⟩ := o.arrive hr ha
    have hp : arrivesOn m ⟨pc, .arrive m (n * bytes) 1 rel sc⟩ = true := by
      simp [arrivesOn, sourceArrive]
    have hlen := len_of_get he
    have hc := countP_take_le_length (arrivesOn m) (X.tr y) j
    have hcj : ((X.tr y).take j).countP (arrivesOn m) ≤ j :=
      List.countP_le_length.trans (List.length_take_le _ _)
    refine hmem (⟨0, by omega⟩, ((X.tr y).take j).countP (arrivesOn m)) (by simp only at *; omega)
      ?_ (fun _ => ha) (fun h => absurd rfl h)
    rw [hid]
    simp only [it, op, ↓reduceIte, nthEv_eq he hp]
  · obtain ⟨rfl, j, pc, al, sp, hid, he, hm⟩ := o.copy hr ha
    have hp : issuesTo m ⟨pc, .tensorIssue al sp⟩ = true := by simp [issuesTo, hm]
    have hlen := len_of_get he
    set c := ((X.tr y).take j).countP (issuesTo m) with hc
    have hcj : c ≤ j := List.countP_le_length.trans (List.length_take_le _ _)
    have hdm := Nat.div_add_mod c n
    have hlt := Nat.mod_lt c hn
    have hdl := Nat.div_le_self c n
    refine hmem (⟨c % n + 1, by omega⟩, c / n) (by simp only at *; omega) ?_
      (fun h => by simp at h) (fun _ => ha)
    rw [hid]
    simp only [it, op, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, hdm]
    rw [hc, nthEv_eq he hp]

theorem counted (o : Obj X m y n bytes) : Counted X m (S X m y n bytes) (it X m y n) where
  record _ hx := (o.source hx).1
  init := ⟨1, o.init⟩
  noInval := o.noInval

/-- The issue of an item precedes it. -/
theorem issue (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) {x : Fin (n + 1) × Nat}
    (hx : x ∈ S X m y n bytes) :
    Relation.ReflTransGen (DepStep L K X) (.thread (op X m y n x.1 x.2), false)
      (it X m y n x.1 x.2, false) := by
  obtain ⟨⟨i, r, hi, hid, -⟩, -, h1⟩ := o.source hx
  by_cases hk : x.1.val = 0
  · have h : it X m y n x.1 x.2 = .thread (op X m y n x.1 x.2) := by simp [it, hk]
    rw [h]
  · obtain ⟨⟨pc, al, sp, he, -⟩, -⟩ := h1 hk
    have h : it X m y n x.1 x.2 = .async (op X m y n x.1 x.2) (.notify .load) := by
      simp [it, hk]
    rw [h]
    have hp := object_record_present hX.tma (List.mem_of_getElem? hi)
    rw [hid, h] at hp
    obtain ⟨o, ho, hn⟩ := id hp
    obtain ⟨x', y', k', hwp⟩ := tensor_write_present hX.effectValidity ho hn
    exact (((Relation.TransGen.single (DepStep.issue (L := L) (K := K)
      (p := .write (.load x' y' k')) ⟨_, he⟩ hwp (fun _ h => by cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h))).tail (DepStep.node hwp)).tail (DepStep.stage
        (c := (.async (op X m y n x.1 x.2) (.notify .load), false))
        (.inr ⟨rfl, rfl, rfl, rfl, hwp, hp⟩))).to_reflTransGen

theorem noInc (o : Obj X m y n bytes) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => o.incr r hr hi

open Classical in
set_option maxHeartbeats 1000000 in
/-- **The phase a poll observes holds `n + 1` counted items**: one arrival, and `n` completions
since the phase's transaction updates cancel. -/
theorem card_phase (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hn : 0 < n)
    (hb0 : 0 < bytes) {g j δ : Nat} (hδ' : δ ≤ 1)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) δ) (hδ : δ ≤ j)
    (hj : j < okPolls m (X.tr g)) :
    n + 1 ≤ ((S X m y n bytes).filter
      (fun x => Counted.ph X m (it X m y n) x = Unit.obsOf X m g j)).card := by
  obtain ⟨iw, w, st, hiw, -, -, -, hst, hpos, -, hoF⟩ :=
    o.counted.poll_obs hX hδ' hAlt hδ hj
  set log := X.objects m with hlog
  obtain ⟨q, hq⟩ : ∃ q, st.phase = q + 1 := ⟨st.phase - 1, by omega⟩
  rw [hq, Nat.add_sub_cancel] at hoF
  have hch : CheckedLog log := X.objects_checked hX m
  have hni := o.noInval
  have hiwl : iw ≤ log.length := (List.getElem?_eq_some_iff.mp hiw).1.le
  -- the phase's arrival
  let U := (Finset.range log.length).filter (fun k => UnitArrivalIn log q k)
  have hU : U.card = 1 := hch.card_unit_arrivals_phase hni (n := 1) (q := q)
    (fun i r c' tx hr hf ha => (o.arrive hr ha).1)
    (fun i st' _ hs => PairTmaRing.expected_of_init hX o.init hni hs)
    o.noInc hiwl hst
    (by omega)
  -- the phase's completions
  let C := (Finset.range log.length).filter (fun k => ∃ r, log[k]? = some r ∧
    r.action = .completeTx bytes ∧ r.fault = none ∧ phaseAt log k = some q)
  obtain ⟨e, he, hce⟩ := hch.crossing hni (c := q) hiwl hst (by omega)
  obtain ⟨s0, s1, hs0, hs0p, hs1, hs1p⟩ := hce
  have hel : e < log.length := by have := (List.getElem?_eq_some_iff.mp hiw).1; omega
  have hsum := (hch.completion_sums hni hel ⟨s0, s1, hs0, hs0p, hs1, hs1p⟩).1
  -- positions of phase `q` are at most `e`
  have hle : ∀ k, k < log.length → phaseAt log k = some q → k < e + 1 := by
    intro k hk hph
    by_contra hge
    obtain ⟨t, htk, hlt⟩ := hch.phase_mono hni (show e + 1 ≤ k by omega) hk.le hs1
    simp only [phaseAt, htk, Option.map_some, Option.some.injEq] at hph
    omega
  have hUsub : U ⊆ Finset.range (e + 1) := by
    intro k hk
    obtain ⟨hkl, -, -, -, -, -, hph⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_range.mpr (hle k (Finset.mem_range.mp hkl) hph)
  have hCsub : C ⊆ Finset.range (e + 1) := by
    intro k hk
    obtain ⟨hkl, -, -, -, -, hph⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_range.mpr (hle k (Finset.mem_range.mp hkl) hph)
  have hpoint : ∀ k ∈ Finset.range (e + 1),
      (if phaseAt log k = some q then txDeltaAt log k else 0) =
        ((n * bytes) : Int) * (if k ∈ U then (1 : Int) else 0) -
          (bytes : Int) * (if k ∈ C then (1 : Int) else 0) := by
    intro k hk
    have hkl : k < log.length := by have := Finset.mem_range.mp hk; omega
    obtain ⟨r, hr⟩ : ∃ r, log[k]? = some r := ⟨_, List.getElem?_eq_getElem hkl⟩
    have hrm := List.mem_of_getElem? hr
    have hdelta : txDeltaAt log k = r.txDelta := by simp [txDeltaAt, hr]
    by_cases hph : phaseAt log k = some q
    · rw [ite_eq_left hph, hdelta]
      by_cases hf : r.fault = none
      · cases ha : r.action with
        | inval => exact (hni r hrm ha).elim
        | increment =>
          exact (o.incr r hrm ha).elim
        | arrive n tx =>
          obtain ⟨rfl, rfl, -⟩ := o.arrive hr ha
          have hkU : k ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, r, _, hr, ha,
            hf, hph⟩
          have hkC : k ∉ C := by
            intro hkC
            obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          rw [ite_eq_left hkU, ite_eq_right hkC]
          simp [Record.txDelta, hf, ha, Action.txDelta]
        | completeTx n =>
          obtain ⟨rfl, -⟩ := o.copy hr ha
          have hkC : k ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, r, hr, ha, hf, hph⟩
          have hkU : k ∉ U := by
            intro hkU
            obtain ⟨-, r', tx', hr', ha', -⟩ := Finset.mem_filter.mp hkU
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          rw [ite_eq_left hkC, ite_eq_right hkU]
          simp [Record.txDelta, hf, ha, Action.txDelta]
        | init n =>
          have hkU : k ∉ U := by
            intro hkU
            obtain ⟨-, r', tx', hr', ha', -⟩ := Finset.mem_filter.mp hkU
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          have hkC : k ∉ C := by
            intro hkC
            obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          rw [ite_eq_right hkU, ite_eq_right hkC]
          simp [Record.txDelta, hf, ha, Action.txDelta]
        | pollParity p ok =>
          have hkU : k ∉ U := by
            intro hkU
            obtain ⟨-, r', tx', hr', ha', -⟩ := Finset.mem_filter.mp hkU
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          have hkC : k ∉ C := by
            intro hkC
            obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          rw [ite_eq_right hkU, ite_eq_right hkC]
          simp [Record.txDelta, hf, ha, Action.txDelta]
      · have hkU : k ∉ U := by
          intro hkU
          obtain ⟨-, r', tx', hr', -, hf', -⟩ := Finset.mem_filter.mp hkU
          rw [hr] at hr'; cases hr'; exact hf hf'
        have hkC : k ∉ C := by
          intro hkC
          obtain ⟨-, r', hr', -, hf', -⟩ := Finset.mem_filter.mp hkC
          rw [hr] at hr'; cases hr'; exact hf hf'
        rw [ite_eq_right hkU, ite_eq_right hkC]
        simp [Record.txDelta, hf]
    · have hkU : k ∉ U := by
        intro hkU
        obtain ⟨-, r', tx', -, -, -, hph'⟩ := Finset.mem_filter.mp hkU
        exact hph hph'
      have hkC : k ∉ C := by
        intro hkC
        obtain ⟨-, r', -, -, -, hph'⟩ := Finset.mem_filter.mp hkC
        exact hph hph'
      rw [ite_eq_right hph, ite_eq_right hkU, ite_eq_right hkC]
      simp
  have hcardU : ((U.card : Nat) : Int) =
      ∑ k ∈ Finset.range (e + 1), if k ∈ U then (1 : Int) else 0 := by
    rw [Finset.card_eq_sum_ite hUsub]; push_cast; rfl
  have hcardC : ((C.card : Nat) : Int) =
      ∑ k ∈ Finset.range (e + 1), if k ∈ C then (1 : Int) else 0 := by
    rw [Finset.card_eq_sum_ite hCsub]; push_cast; rfl
  have htx : (0 : Int) = ((n * bytes) : Int) * (U.card : Int) - (bytes : Int) * (C.card : Int) := by
    rw [← hsum, phaseTx, Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hcardU, hcardC]
  rw [hU] at htx
  have hC : C.card = n := by
    push_cast at htx
    have h2 : (bytes : Int) * ((n : Int) - (C.card : Int)) = 0 := by linear_combination -htx
    rcases mul_eq_zero.mp h2 with h | h
    · have := hb0; omega
    · omega
  -- the arrival and the copies, as many items
  have hdisj : Disjoint U C := by
    rw [Finset.disjoint_left]
    intro k hkU hkC
    obtain ⟨-, r, tx, hr, ha, -⟩ := Finset.mem_filter.mp hkU
    obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
    rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
  have h7 : (U ∪ C).card = n + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hU, hC, Nat.add_comm]
  refine le_trans (le_of_eq h7.symm) ?_
  refine PairTmaRing.card_le_of_rel _ _
    (fun k x => ∃ r, log[k]? = some r ∧ r.id = it X m y n x.1 x.2)
    (fun k hk => ?_) (fun k hk k' hk' x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  have hk' : ∃ r, log[k]? = some r ∧ r.fault = none ∧
      ((∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) ∧
      phaseAt log k = some q := by
    rcases Finset.mem_union.mp hk with hkU | hkC
    · obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hkU
      exact ⟨r, hr, hf, .inl ⟨1, tx, ha⟩, hph⟩
    · obtain ⟨-, r, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hkC
      exact ⟨r, hr, hf, .inr ⟨bytes, ha⟩, hph⟩
  obtain ⟨r, hr, hf, hu, hph⟩ := hk'
  obtain ⟨x, hx, hid⟩ := o.item hr hf hu hn
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, r, hr, hid⟩
  unfold Counted.ph
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph, hoF]

end Obj
end
end PTX.MbarRing.TmaUnits
