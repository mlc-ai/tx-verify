-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.ItemFacts
public import Lemmas.MBarrier.MBarrierRound
public import Lemmas.MBarrier.MBarrierTransactions

@[expose] public section

/-! # A pair TMA ring slot as a ring of items

A proof tool. Under `Hyp`, slot `S` is a `MbarRing.Items.Ring` (`ring`) with the items of
`Items.lean`. The thread layer gives the guards: a producer's item of use `u` follows its polls
of its empty barrier for the uses `1, …, u`, a consumer's commit of use `t` its polls of the
full barrier for the uses `0, …, t`, and the polls spin. Each object is read through its own
history: a successful poll observes every counted record of the phase it observes
(`Consistent.observed_of_phase`); a completed phase of an empty barrier holds `nc`
notifications (`card_unit_arrivals_phase`), and one of the full barrier one arrival and, since
its transaction counter returns to zero, `2 n` completions (`completion_sums`), so `1 + 2 n`
items (`fullF_card`); and a poller's polls observe increasing phases (`Poll.observed_lt`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

/-- Counting by a relation: a finset each of whose elements is related to an element of `T`,
no element of `T` to two of them, is no larger than `T`. -/
theorem card_le_of_rel {α β : Type} [DecidableEq α] (S : Finset α) (T : Finset β)
    (R : α → β → Prop) (hex : ∀ a ∈ S, ∃ b ∈ T, R a b)
    (huniq : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ T, R a b → R a' b → a = a') : S.card ≤ T.card := by
  have h := MbarRing.Slot.length_le_card_of_rel S.toList S.nodup_toList T R
    (fun a ha => hex a (Finset.mem_toList.mp ha))
    (fun a ha a' ha' b hb => huniq a (Finset.mem_toList.mp ha) a' (Finset.mem_toList.mp ha') b hb)
  simpa using h

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {nc : Nat} {S : Slot nc}

/-! ### The thread layer -/

theorem guardP (H : Hyp L K A X S) {x : Kind S.n × Nat} (hx : x ∈ SF X S) {n : Nat} (hn : n ≤ x.2) :
    Resumes K X (wE X S (kOwner S.n x.1) n) (opF X S x.1 x.2) := by
  obtain ⟨-, ⟨e, he, -, -⟩, hb⟩ := SF_op H hx
  exact MbarRing.Poll.guard H.spins (len_of_get he) (by simp only [opF] at hb ⊢; omega)

theorem guardM (H : Hyp L K A X S) {a : Fin 2} {y : Fin nc × Nat} (hy : y ∈ SE X S a) {j : Nat}
    (hj : j ≤ y.2) :
    Resumes K X (wF X S y.1 j) (cm X S y.1 y.2) := by
  obtain ⟨-, ⟨pc, sp, he, -⟩, hb⟩ := SE_op H hy
  exact MbarRing.Poll.guard H.spins (len_of_get he) (by simp only [cm] at hb ⊢; omega)

theorem issueF (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {x : Kind S.n × Nat}
    (hx : x ∈ SF X S) :
    Relation.ReflTransGen (DepStep L K X) (.thread (opF X S x.1 x.2), false)
      (itF X S x.1 x.2, false) := by
  obtain ⟨⟨i, r, hi, hid, -⟩, ⟨e, he, -⟩, -⟩ := SF_op H hx
  by_cases hk : x.1.val = 0
  · have h : itF X S x.1 x.2 = .thread (opF X S x.1 x.2) := by simp [itF, hk]
    rw [h]
  · have h : itF X S x.1 x.2 = .async (opF X S x.1 x.2) (.notify .load) := by
      simp [itF, hk]
    rw [h]
    have hp := object_record_present hX.tma (List.mem_of_getElem? hi)
    rw [hid, h] at hp
    obtain ⟨o, ho, hn⟩ := id hp
    obtain ⟨x', y', k', hwp⟩ := tensor_write_present hX.effectValidity ho hn
    exact (((Relation.TransGen.single (DepStep.issue (L := L) (K := K)
      (p := .write (.load x' y' k')) ⟨_, he⟩ hwp (fun _ h => by cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h))).tail (DepStep.node hwp)).tail (DepStep.stage
        (c := (.async (opF X S x.1 x.2) (.notify .load), false))
        (.inr ⟨rfl, rfl, rfl, rfl, hwp, hp⟩))).to_reflTransGen

theorem issueE (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {y : Fin nc × Nat}
    (hy : y ∈ SE X S a) :
    Relation.ReflTransGen (DepStep L K X) (.thread (cm X S y.1 y.2), false)
      (note X S y.1 a y.2, false) := by
  obtain ⟨⟨i, r, hi, hid, -⟩, ⟨pc, sp, he, -⟩, -⟩ := SE_op H hy
  have hp := object_record_present hX.tma (List.mem_of_getElem? hi)
  rw [hid] at hp
  exact .single (.inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hp, trivial⟩))

/-! ### The objects -/

theorem counter_item {r : Record Ref} {x : Kind S.n × Nat}
    (h0 : x.1.val = 0 → r.action = .arrive 1 S.tx)
    (h1 : x.1.val ≠ 0 → r.action = .completeTx S.bytes) : CounterUpdate r.action := by
  by_cases hk : x.1.val = 0
  · rw [h0 hk]; trivial
  · rw [h1 hk]; trivial

theorem obsF (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {j : Nat}
    (hw : X.RefPresent (.thread (wF X S b j))) {x : Kind S.n × Nat} (hx : x ∈ SF X S)
    (hph : phF X S x = oF X S b j) :
    Witness L X (itF X S x.1 x.2) (wF X S b j) := by
  have hj := MbarRing.Poll.nth_present.mp hw
  obtain ⟨iw, w, st, hiw, hwid, hww, -, -, -, -, -, hobs, hoF⟩ := F_poll hX H hj
  obtain ⟨⟨i, r, hi, hid, hf, h0, h1⟩, -⟩ := SF_op H hx
  obtain ⟨-, sd, hsd, -⟩ := state_of_init hX H.full_init H.full_noInval hi (by
      intro n
      by_cases hk : x.1.val = 0
      · rw [h0 hk]; simp
      · rw [h1 hk]; simp)
  have hsd' : stateBefore (X.objects S.full) i = some sd := hsd
  have hp : phaseAt (X.objects S.full) i = some sd.phase := by
    simp [phaseAt, hsd']
  have hpo := MbarRing.Poll.phaseOf_eq hX hi hp
  unfold phF at hph
  rw [← hid, hpo, hoF] at hph
  rw [hph] at hp
  have h := Consistent.observed_of_phase hX (H.full_noInval) hi hf
      (counter_item h0 h1) hiw hww
    hp hobs
  rw [hid, hwid] at h
  exact Witness.of_mbarObserved h

theorem obsE (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n : Nat} (hn : 1 ≤ n)
    (hw : X.RefPresent (.thread (wE X S a n))) {y : Fin nc × Nat} (hy : y ∈ SE X S a)
    (hph : phE X S a y = oE X S a n) :
    Witness L X (note X S y.1 a y.2) (wE X S a n) := by
  have hj := MbarRing.Poll.nth_present.mp hw
  obtain ⟨iw, w, st, hiw, hwid, hww, -, -, -, -, -, hobs, hoE⟩ := E_poll hX H hn hj
  obtain ⟨⟨i, r, hi, hid, hf, ha⟩, -⟩ := SE_op H hy
  obtain ⟨-, sd, hsd, -⟩ := state_of_init hX (H.empty_init a) (H.empty_noInval a) hi
    (by intro n; rw [ha]; simp)
  have hsd' : stateBefore (X.objects (S.empty a)) i = some sd := hsd
  have hp : phaseAt (X.objects (S.empty a)) i = some sd.phase := by
    simp [phaseAt, hsd']
  have hpo := MbarRing.Poll.phaseOf_eq hX hi hp
  unfold phE at hph
  rw [← hid, hpo, hoE] at hph
  rw [hph] at hp
  have hcu : CounterUpdate r.action := by rw [ha]; trivial
  have h := Consistent.observed_of_phase hX (H.empty_noInval a) hi hf hcu hiw hww hp hobs
  rw [hid, hwid] at h
  exact Witness.of_mbarObserved h

theorem ltF (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {j j' : Nat}
    (hjj : j < j')
    (hw : X.RefPresent (.thread (wF X S b j'))) :
    X.RefPresent (.thread (wF X S b j)) ∧ oF X S b j < oF X S b j' := by
  have hj' := MbarRing.Poll.nth_present.mp hw
  exact ⟨MbarRing.Poll.nth_present.mpr (by omega), MbarRing.Poll.observed_lt hX (by decide)
    (full_poll_clean hX H) (H.full_noInval) (F_alt hX H _)
        (Nat.zero_le _) hjj hj'⟩

theorem ltE (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n n' : Nat} (hn : 1 ≤ n)
    (hnn : n < n') (hw : X.RefPresent (.thread (wE X S a n'))) :
    X.RefPresent (.thread (wE X S a n)) ∧ oE X S a n < oE X S a n' := by
  have hj' := MbarRing.Poll.nth_present.mp hw
  exact ⟨MbarRing.Poll.nth_present.mpr (by omega), MbarRing.Poll.observed_lt hX (le_refl 1)
    (empty_poll_clean hX H) (H.empty_noInval a) (E_alt hX H _) hn hnn hj'⟩

/-- The full barrier has no pending-count increment. -/
theorem full_noIncrement (H : Hyp L K A X S) :
    incrementsBefore (X.objects S.full) (X.objects S.full).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases H.full_src r hr with
    | init ha | poll _ _ ha | arrive _ _ ha _ | copy _ _ _ ha => rw [hi] at ha; cases ha

/-- An empty barrier has no pending-count increment. -/
theorem empty_noIncrement (H : Hyp L K A X S) (a : Fin 2) :
    incrementsBefore (X.objects (S.empty a)) (X.objects (S.empty a)).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases H.empty_src a r hr with
    | init ha | poll _ _ ha | notify _ _ _ _ ha _ => rw [hi] at ha; cases ha

/-- A completed phase of an empty barrier, the one producer `a`'s poll for use `n` observes,
holds `nc` counted notifications. -/
theorem fullE_card (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n)
    (hw : X.RefPresent (.thread (wE X S a n))) :
    nc ≤ ((SE X S a).filter (fun y => phE X S a y = oE X S a n)).card := by
  classical
  have hj := MbarRing.Poll.nth_present.mp hw
  obtain ⟨iw, w, st, hiw, -, -, -, -, -, hst, hpos, -, hoE⟩ := E_poll hX H hn hj
  set log := X.objects (S.empty a) with hlog
  have hch : CheckedLog log := X.objects_checked hX (S.empty a)
  have hni := H.empty_noInval a
  have hcard := hch.card_unit_arrivals_phase hni (n := nc) (q := st.phase - 1)
    (fun i r c' tx hr hf ha => (notify_consumer H (List.mem_of_getElem? hr) ha).1)
    (fun i st' _ hs => expected_of_init hX (H.empty_init a) hni hs) (empty_noIncrement H a)
    (List.getElem?_eq_some_iff.mp hiw).1.le hst (by omega)
  refine le_trans (le_of_eq hcard.symm) ?_
  refine card_le_of_rel _ _ (fun k y => ∃ r, log[k]? = some r ∧ r.id = note X S y.1 a y.2)
    (fun k hk => ?_) (fun k hk k' hk' y _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hk
  obtain ⟨-, y, hy, hid⟩ := empty_item H (List.mem_of_getElem? hr) hf ha
  refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, r, hr, hid⟩
  unfold phE
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph, hoE]

/-- A completed phase of the full barrier, the one consumer `b`'s poll for use `j` observes,
holds `1 + 2 n` counted items: one arrival, and `2 n` completions since the phase's
transaction updates cancel. -/
theorem fullF_card (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {j : Nat}
    (hw : X.RefPresent (.thread (wF X S b j))) :
    1 + 2 * S.n ≤ ((SF X S).filter (fun x => phF X S x = oF X S b j)).card := by
  classical
  have hj := MbarRing.Poll.nth_present.mp hw
  obtain ⟨iw, w, st, hiw, -, -, -, -, -, hst, hpos, -, hoF⟩ := F_poll hX H hj
  set log := X.objects S.full with hlog
  obtain ⟨q, hq⟩ : ∃ q, st.phase = q + 1 := ⟨st.phase - 1, by omega⟩
  rw [hq, Nat.add_sub_cancel] at hoF
  have hch : CheckedLog log := X.objects_checked hX S.full
  have hni := H.full_noInval
  have hiwl : iw ≤ log.length := (List.getElem?_eq_some_iff.mp hiw).1.le
  -- the phase's arrival
  let U := (Finset.range log.length).filter (fun k => UnitArrivalIn log q k)
  have hU : U.card = 1 := hch.card_unit_arrivals_phase hni (n := 1) (q := q)
    (fun i r c' tx hr hf ha => (arrival_producer H (List.mem_of_getElem? hr) ha).1)
    (fun i st' _ hs => expected_of_init hX H.full_init hni hs) (full_noIncrement H) hiwl hst
    (by omega)
  -- the phase's completions
  let C := (Finset.range log.length).filter (fun k => ∃ r, log[k]? = some r ∧
    r.action = .completeTx S.bytes ∧ r.fault = none ∧ phaseAt log k = some q)
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
        (S.tx : Int) * (if k ∈ U then (1 : Int) else 0) -
          (S.bytes : Int) * (if k ∈ C then (1 : Int) else 0) := by
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
          exfalso
          cases H.full_src r hrm with
          | init ha' | poll _ _ ha' | arrive _ _ ha' _ | copy _ _ _ ha' => rw [ha] at ha'; cases ha'
        | arrive n tx =>
          obtain ⟨rfl, rfl, -⟩ := arrival_producer H hrm ha
          have hkU : k ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, r, S.tx, hr, ha,
            hf, hph⟩
          have hkC : k ∉ C := by
            intro hkC
            obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          rw [ite_eq_left hkU, ite_eq_right hkC]
          simp [Record.txDelta, hf, ha, Action.txDelta]
        | completeTx n =>
          obtain ⟨rfl, -⟩ := completion_producer H hrm ha
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
  have htx : (0 : Int) = (S.tx : Int) * (U.card : Int) - (S.bytes : Int) * (C.card : Int) := by
    rw [← hsum, phaseTx, Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hcardU, hcardC]
  rw [hU] at htx
  have hC : C.card = 2 * S.n := by
    have hB : (S.bytes : Int) * (C.card : Int) = (S.bytes : Int) * ((2 * S.n : Nat) : Int) := by
      unfold Slot.tx at htx; push_cast at htx ⊢; linarith
    exact_mod_cast Int.eq_of_mul_eq_mul_left (by exact_mod_cast H.bytes_pos.ne') hB
  -- the arrival and the copies, as many items
  have hdisj : Disjoint U C := by
    rw [Finset.disjoint_left]
    intro k hkU hkC
    obtain ⟨-, r, tx, hr, ha, -⟩ := Finset.mem_filter.mp hkU
    obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
    rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
  have h7 : (U ∪ C).card = 1 + 2 * S.n := by rw [Finset.card_union_of_disjoint hdisj, hU, hC]
  refine le_trans (le_of_eq h7.symm) ?_
  refine card_le_of_rel _ _ (fun k x => ∃ r, log[k]? = some r ∧ r.id = itF X S x.1 x.2)
    (fun k hk => ?_) (fun k hk k' hk' x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  have hk' : ∃ r, log[k]? = some r ∧ r.fault = none ∧
      ((∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) ∧
      phaseAt log k = some q := by
    rcases Finset.mem_union.mp hk with hkU | hkC
    · obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hkU
      exact ⟨r, hr, hf, .inl ⟨1, tx, ha⟩, hph⟩
    · obtain ⟨-, r, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hkC
      exact ⟨r, hr, hf, .inr ⟨S.bytes, ha⟩, hph⟩
  obtain ⟨r, hr, hf, hu, hph⟩ := hk'
  obtain ⟨x, hx, hid, -⟩ := full_item H (List.mem_of_getElem? hr) hf hu
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, r, hr, hid⟩
  unfold phF
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph, hoF]

/-! ### The ring -/

/-- **Slot `S` as a ring of items.** -/
def ring (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) :
    MbarRing.Items.Ring L K A X 2 nc 1 (fun _ => 1 + 2 * S.n) where
  owner _ := 0
  ownF _ k := kOwner S.n k
  wE := wE X S
  opF _ := opF X S
  itF _ := itF X S
  wF := wF X S
  cm := cm X S
  note := note X S
  SF _ := SF X S
  phF _ := phF X S
  SE := SE X S
  phE := phE X S
  oF := oF X S
  oE := oE X S
  cover _ a := ⟨copyKind S.n a 0 H.n_pos, kOwner_copyKind a 0 _⟩
  guardP _ _ hx _ _ hn := guardP H hx hn
  issueF _ _ hx := issueF hX H hx
  guardM _ _ hy _ hj := guardM H hy hj
  issue _ _ hy := issueE hX H hy
  obsF _ _ hw _ hx hph := obsF hX H hw hx hph
  obsE _ _ hn hw _ hy hph := obsE hX H hn hw hy hph
  fullF _ _ hw := fullF_card hX H hw
  fullE _ _ hn hw := fullE_card hX H hn hw
  ltF _ _ _ hjj hw := ltF hX H hjj hw
  ltE _ _ _ hn hnn hw := ltE hX H hn hnn hw

end
end PTX.PairTmaRing
