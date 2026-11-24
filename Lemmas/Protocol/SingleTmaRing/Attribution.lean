-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.Items

@[expose] public section

/-! # A slot of a single-CTA TMA ring as a ring of items

A proof tool (generalized from the Inkling KV ring). Under `Hyp`, slot `S` is a
`MbarRing.Items.Ring` (`ring`) with the items of `Items.lean`, when a use has at least one copy
and a copy at least one byte. The thread layer gives the guards: a producer's item of use
`u ≥ 1` follows its successful polls of `empty` for the uses `1, …, u`, the consumer's commit of
use `t` its polls of `full` for the uses `0, …, t`, and the polls spin. A completed phase of
`empty` holds one notification, and one of `full` one arrival and, since its transaction counter
returns to zero, `n` completions (`fullF_card`), so `n + 1` items; and a poller's polls observe
increasing phases. -/

namespace PTX.SingleTmaRing
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section


variable {X : Execution} {S : Slot} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {sc : MbarScope}

/-! ### Polls -/

theorem full_poll_clean (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) :
    ∀ q ∈ X.objects S.full, (∃ p ok, q.action = .pollParity p ok) → q.fault = none :=
  PairTmaRing.poll_clean hX H.full_init H.full_noInval

theorem empty_poll_clean (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) :
    ∀ q ∈ X.objects S.empty, (∃ p ok, q.action = .pollParity p ok) → q.fault = none :=
  PairTmaRing.poll_clean hX H.empty_init H.empty_noInval

theorem F_alt (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (g : Nat) :
    SelectedAlternates (objectThreadSelected g) (X.objects S.full) 0 :=
  MbarRing.Poll.alternates hX (full_poll_clean hX H) fun _ _ _ _ _ he => H.full_parity he

theorem E_alt (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (g : Nat) :
    SelectedAlternates (objectThreadSelected g) (X.objects S.empty) (1 - S.δ) :=
  MbarRing.Poll.alternates hX (empty_poll_clean hX H) fun _ _ _ _ _ he => H.empty_parity he

/-- The consumer's successful full poll with `j` earlier ones: its record, which found a state
past phase `0` and observed the phase before it. -/
theorem F_poll (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {b : Fin 1} {j : Nat}
    (hj : j < okPolls S.full (X.tr S.cm)) :
    ∃ i w st, (X.objects S.full)[i]? = some w ∧ w.id = .thread (wF X S b j) ∧
      w.reply.waited = some true ∧ w.fault = none ∧
      objectThreadSelected S.cm w.id = true ∧
      selectedBefore (objectThreadSelected S.cm) (X.objects S.full) i = j ∧
      stateBefore (X.objects S.full) i = some st ∧ 0 < st.phase ∧
      observedAt (X.objects S.full) i = some (st.phase - 1) ∧ oF X S b j = st.phase - 1 := by
  obtain ⟨i, w, p, hi, hwid, -, hww, hwf, hsel⟩ :=
    MbarRing.Poll.record hX (full_poll_clean hX H) hj
  have hs : objectThreadSelected S.cm w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
    H.full_noInval (by decide : 0 ≤ 1) (F_alt hX H _) hi hs hww (by omega)
  refine ⟨i, w, st, hi, hwid, hww, hwf, hs, hsel, hst, hpos, ho, ?_⟩
  unfold oF wF
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hi ho

/-- Producer `a`'s successful empty poll for use `n ≥ 1`: its record, which found a state past
phase `0` and observed the phase before it. -/
theorem E_poll (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n) (hj : n - S.δ < okPolls S.empty (X.tr (S.prod a))) :
    ∃ i w st, (X.objects S.empty)[i]? = some w ∧ w.id = .thread (wE X S a n) ∧
      w.reply.waited = some true ∧ w.fault = none ∧
      objectThreadSelected (S.prod a) w.id = true ∧
      selectedBefore (objectThreadSelected (S.prod a)) (X.objects S.empty) i = n - S.δ ∧
      stateBefore (X.objects S.empty) i = some st ∧ 0 < st.phase ∧
      observedAt (X.objects S.empty) i = some (st.phase - 1) ∧
      oE X S a n = st.phase - 1 := by
  have hδ := H.δ_le
  obtain ⟨i, w, p, hi, hwid, -, hww, hwf, hsel⟩ :=
    MbarRing.Poll.record hX (empty_poll_clean hX H) hj
  have hs : objectThreadSelected (S.prod a) w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
    H.empty_noInval (by omega : 1 - S.δ ≤ 1) (E_alt hX H _) hi hs hww (by rw [hsel]; omega)
  refine ⟨i, w, st, hi, hwid, hww, hwf, hs, hsel, hst, hpos, ho, ?_⟩
  unfold oE wE
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hi ho

/-! ### The thread layer -/

/-- The record of a counted notification, and its consumer's commit: the commit with the use's
count of earlier ones, after more successful full polls of the consumer than the use. -/
theorem SE_op (H : Hyp L K A X S sc) {y : Fin 1 × Nat} (hy : y ∈ SE X S) :
    (∃ (i : Nat) (r : Record Ref), (X.objects S.empty)[i]? = some r ∧
      r.id = note X S y.1 0 y.2 ∧ r.fault = none ∧ r.action = .arrive 1 0) ∧
    (∃ pc sp, X.get (cmE X S y.1 y.2) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = S.empty ∧
      TcCommit.target sp rank0 = some S.empty ∧
      ((X.tr S.cm).take (cmE X S y.1 y.2).2).countP (commitsTo S.empty) = y.2) ∧
    y.2 + 1 ≤ okPolls S.full ((X.tr S.cm).take (cmE X S y.1 y.2).2) := by
  obtain ⟨-, r, hr, hid, hf, ha⟩ := Finset.mem_filter.mp hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  refine ⟨⟨i, r, hi, hid, hf, ha⟩, ?_⟩
  obtain ⟨-, -, j, pc, sp, hid', he, hm, htg, hcb⟩ := notify_source H hr ha
  rw [hid'] at hid
  simp only [note, cmE, Ref.async.injEq, Prod.mk.injEq, and_true] at hid
  obtain ⟨-, hj⟩ := hid
  have hp : commitsTo S.empty ⟨pc, .tc (.commit sp)⟩ = true := by simp [commitsTo, hm]
  have hcnt := (nthEv_spec_of_get (hj ▸ he)).2
  rw [← hj] at hcnt
  simp only [cmE]
  rw [← hj]
  refine ⟨⟨pc, sp, he, hm, htg, hcnt⟩, ?_⟩
  rw [hcnt] at hcb
  exact hcb

/-- A guard of the loader's items: the item of use `u ≥ 1` follows the producer's polls for the
uses `1, …, u`. -/
theorem guardP (H : Hyp L K A X S sc) {x : Kind S × Nat} (hx : x ∈ SF X S) {n : Nat} (h1 : 1 ≤ n)
    (hn : n ≤ x.2) :
    Resumes K X (wE X S (kOwner x.1) n) (opF X S x.1 x.2) := by
  obtain ⟨-, ⟨e, he⟩, hs⟩ := SF_op H hx
  have hδ := H.δ_le
  rcases hs with ⟨-, hu⟩ | ⟨j, hj, hb⟩
  · omega
  · simp only [wE]
    rw [hj] at he ⊢
    exact MbarRing.Poll.guard H.spins (len_of_get he) (by omega)

theorem guardM (H : Hyp L K A X S sc) {y : Fin 1 × Nat} (hy : y ∈ SE X S) {j : Nat} (hj : j ≤ y.2) :
    Resumes K X (wF X S y.1 j) (cmE X S y.1 y.2) := by
  obtain ⟨-, ⟨pc, sp, he, -⟩, hb⟩ := SE_op H hy
  exact MbarRing.Poll.guard H.spins (len_of_get he) (by simp only [cmE] at hb ⊢; omega)

theorem issueF (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {x : Kind S × Nat}
    (hx : x ∈ SF X S) :
    Relation.ReflTransGen (DepStep L K X) (.thread (opF X S x.1 x.2), false)
      (itF X S x.1 x.2, false) := by
  obtain ⟨⟨i, r, hi, hid, -⟩, ⟨e, he⟩, -⟩ := SF_op H hx
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

theorem issueE (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {y : Fin 1 × Nat}
    (hy : y ∈ SE X S) :
    Relation.ReflTransGen (DepStep L K X) (.thread (cmE X S y.1 y.2), false)
      (note X S y.1 0 y.2, false) := by
  obtain ⟨⟨i, r, hi, hid, -⟩, ⟨pc, sp, he, -⟩, -⟩ := SE_op H hy
  have hp := object_record_present hX.tma (List.mem_of_getElem? hi)
  rw [hid] at hp
  exact .single (.inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hp, trivial⟩))

/-! ### The objects -/

theorem counter_item {r : Record Ref} {x : Kind S × Nat}
    (h0 : x.1.val = 0 → r.action = .arrive 1 S.tx)
    (h1 : x.1.val ≠ 0 → r.action = .completeTx S.bytes) : CounterUpdate r.action := by
  by_cases hk : x.1.val = 0
  · rw [h0 hk]; trivial
  · rw [h1 hk]; trivial

theorem obsF (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {b : Fin 1} {j : Nat}
    (hw : X.RefPresent (.thread (wF X S b j))) {x : Kind S × Nat} (hx : x ∈ SF X S)
    (hph : phF X S x = oF X S b j) :
    Witness L X (itF X S x.1 x.2) (wF X S b j) := by
  have hj := MbarRing.Poll.nth_present.mp hw
  obtain ⟨iw, w, st, hiw, hwid, hww, -, -, -, -, -, hobs, hoF⟩ := F_poll hX H hj
  obtain ⟨⟨i, r, hi, hid, hf, h0, h1⟩, -⟩ := SF_op H hx
  obtain ⟨-, sd, hsd, -⟩ := PairTmaRing.state_of_init hX H.full_init H.full_noInval hi (by
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

theorem obsE (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n)
    (hw : X.RefPresent (.thread (wE X S a n))) {y : Fin 1 × Nat} (hy : y ∈ SE X S)
    (hph : phE X S y = oE X S a n) :
    Witness L X (note X S y.1 a y.2) (wE X S a n) := by
  have hj := MbarRing.Poll.nth_present.mp hw
  obtain ⟨iw, w, st, hiw, hwid, hww, -, -, -, -, -, hobs, hoE⟩ := E_poll hX H hn hj
  obtain ⟨⟨i, r, hi, hid, hf, ha⟩, -⟩ := SE_op H hy
  obtain ⟨-, sd, hsd, -⟩ := PairTmaRing.state_of_init hX H.empty_init H.empty_noInval hi
    (by intro n; rw [ha]; simp)
  have hsd' : stateBefore (X.objects S.empty) i = some sd := hsd
  have hp : phaseAt (X.objects S.empty) i = some sd.phase := by
    simp [phaseAt, hsd']
  have hpo := MbarRing.Poll.phaseOf_eq hX hi hp
  unfold phE at hph
  rw [← hid, hpo, hoE] at hph
  rw [hph] at hp
  have hcu : CounterUpdate r.action := by rw [ha]; trivial
  have h := Consistent.observed_of_phase hX (H.empty_noInval) hi hf hcu hiw hww hp hobs
  rw [hid, hwid] at h
  simp only [note] at h ⊢
  exact Witness.of_mbarObserved h

theorem ltF (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {b : Fin 1} {j j' : Nat}
    (hjj : j < j') (hw : X.RefPresent (.thread (wF X S b j'))) :
    X.RefPresent (.thread (wF X S b j)) ∧ oF X S b j < oF X S b j' := by
  have hj' := MbarRing.Poll.nth_present.mp hw
  exact ⟨MbarRing.Poll.nth_present.mpr (by omega), MbarRing.Poll.observed_lt hX (by decide)
    (full_poll_clean hX H) (H.full_noInval) (F_alt hX H _)
        (Nat.zero_le _) hjj hj'⟩

theorem ltE (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {a : Fin 2} {n n' : Nat}
    (hn : 1 ≤ n) (hnn : n < n') (hw : X.RefPresent (.thread (wE X S a n'))) :
    X.RefPresent (.thread (wE X S a n)) ∧ oE X S a n < oE X S a n' := by
  have hδ := H.δ_le
  have hj' := MbarRing.Poll.nth_present.mp hw
  refine ⟨MbarRing.Poll.nth_present.mpr (by omega), ?_⟩
  exact MbarRing.Poll.observed_lt hX (by omega : 1 - S.δ ≤ 1)
    (empty_poll_clean hX H) (H.empty_noInval) (E_alt hX H _) (by omega) (by omega) hj'

/-- The full barrier has no pending-count increment. -/
theorem full_noIncrement (H : Hyp L K A X S sc) :
    incrementsBefore (X.objects S.full) (X.objects S.full).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases H.full_src r hr with
    | init ha | poll _ _ ha | arrive _ _ ha _ | preArrive _ _ _ ha | copy _ _ _ ha _
    | preCopy _ _ _ _ ha => rw [hi] at ha; cases ha

/-- The empty barrier has no pending-count increment. -/
theorem empty_noIncrement (H : Hyp L K A X S sc) :
    incrementsBefore (X.objects S.empty) (X.objects S.empty).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases H.empty_src r hr with
    | init ha | poll _ _ ha | notify _ _ _ _ ha _ => rw [hi] at ha; cases ha

/-- A completed phase of the empty barrier, the one producer `a`'s poll for use `n` observes,
holds one counted notification. -/
theorem fullE_card (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n) (hw : X.RefPresent (.thread (wE X S a n))) :
    1 ≤ ((SE X S).filter (fun y => phE X S y = oE X S a n)).card := by
  classical
  have hj := MbarRing.Poll.nth_present.mp hw
  obtain ⟨iw, w, st, hiw, -, -, -, -, -, hst, hpos, -, hoE⟩ := E_poll hX H hn hj
  set log := X.objects S.empty with hlog
  have hch : CheckedLog log := X.objects_checked hX S.empty
  have hni := H.empty_noInval
  have hcard := hch.card_unit_arrivals_phase hni (n := 1) (q := st.phase - 1)
    (fun i r c' tx hr hf ha => (notify_source H (List.mem_of_getElem? hr) ha).1)
    (fun i st' _ hs => PairTmaRing.expected_of_init hX H.empty_init hni hs) (empty_noIncrement H)
    (List.getElem?_eq_some_iff.mp hiw).1.le hst (by omega)
  refine le_trans (le_of_eq hcard.symm) ?_
  refine PairTmaRing.card_le_of_rel _ _
    (fun k y => ∃ r, log[k]? = some r ∧ r.id = note X S y.1 0 y.2)
    (fun k hk => ?_) (fun k hk k' hk' y _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨-, r, tx, hr, ha, hf, hph⟩ := Finset.mem_filter.mp hk
  obtain ⟨-, y, hy, hid⟩ := empty_item H (List.mem_of_getElem? hr) hf ha
  refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, r, hr, hid⟩
  unfold phE
  rw [← hid, MbarRing.Poll.phaseOf_eq hX hr hph, hoE]

/-- A completed phase of the full barrier, the one consumer `b`'s poll for use `j` observes,
holds nine counted items: one arrival, and eight completions since the phase's
transaction updates cancel. -/
theorem fullF_card (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) {b : Fin 1}
    {j : Nat}
    (hw : X.RefPresent (.thread (wF X S b j))) :
    S.n + 1 ≤ ((SF X S).filter (fun x => phF X S x = oF X S b j)).card := by
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
    (fun i r c' tx hr hf ha => (arrival_source H (List.mem_of_getElem? hr) ha).1)
    (fun i st' _ hs => PairTmaRing.expected_of_init hX H.full_init hni hs)
    (full_noIncrement H) hiwl hst
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
          | init ha' | poll _ _ ha' | arrive _ _ ha' _ | preArrive _ _ _ ha' | copy _ _ _ ha' _
          | preCopy _ _ _ _ ha' => rw [ha] at ha'; cases ha'
        | arrive n tx =>
          obtain ⟨rfl, rfl, -⟩ := arrival_source H hrm ha
          have hkU : k ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, r, S.tx, hr, ha,
            hf, hph⟩
          have hkC : k ∉ C := by
            intro hkC
            obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
            rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
          rw [ite_eq_left hkU, ite_eq_right hkC]
          simp [Record.txDelta, hf, ha, Action.txDelta]
        | completeTx n =>
          obtain ⟨rfl, -⟩ := completion_source H hrm ha
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
  have hC : C.card = S.n := by
    simp only [Slot.tx] at htx
    push_cast at htx
    have h2 : (S.bytes : Int) * ((S.n : Int) - (C.card : Int)) = 0 := by linear_combination -htx
    rcases mul_eq_zero.mp h2 with h | h
    · have := hP.2.1; omega
    · omega
  -- the arrival and the copies, as many items
  have hdisj : Disjoint U C := by
    rw [Finset.disjoint_left]
    intro k hkU hkC
    obtain ⟨-, r, tx, hr, ha, -⟩ := Finset.mem_filter.mp hkU
    obtain ⟨-, r', hr', ha', -⟩ := Finset.mem_filter.mp hkC
    rw [hr] at hr'; cases hr'; rw [ha] at ha'; cases ha'
  have h7 : (U ∪ C).card = S.n + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hU, hC, Nat.add_comm]
  refine le_trans (le_of_eq h7.symm) ?_
  refine PairTmaRing.card_le_of_rel _ _ (fun k x => ∃ r, log[k]? = some r ∧ r.id = itF X S x.1 x.2)
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
def ring (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) :
    MbarRing.Items.Ring L K A X 2 1 1 (fun _ => S.n + 1) where
  owner _ := 0
  ownF _ k := kOwner k
  wE := wE X S
  opF _ := opF X S
  itF _ := itF X S
  wF := wF X S
  cm := cmE X S
  note := note X S
  SF _ := SF X S
  phF _ := phF X S
  SE _ := SE X S
  phE _ := phE X S
  oF := oF X S
  oE := oE X S
  cover _ a := by
    fin_cases a
    · exact ⟨⟨0, by omega⟩, by simp [kOwner]⟩
    · exact ⟨⟨1, by have := hP.1; omega⟩, by simp [kOwner]⟩
  guardP _ _ hx _ h1 hn := guardP H hx h1 hn
  issueF _ _ hx := issueF hX H hx
  guardM _ _ hy _ hj := guardM H hy hj
  issue _ _ hy := issueE hX H hy
  obsF _ _ hw _ hx hph := obsF hX H hw hx hph
  obsE _ _ hn hw _ hy hph := obsE hX H hn hw hy hph
  fullF _ _ hw := fullF_card hX H hP hw
  fullE _ _ hn hw := fullE_card hX H hn hw
  ltF _ _ _ hjj hw := ltF hX H hjj hw
  ltE _ _ _ hn hnn hw := ltE hX H hn hnn hw

/-! ### What the attribution says -/

/-- Every non-faulting arrival of the full barrier is a unit arrival of a counted item of kind
`0`. -/
theorem full_count (H : Hyp L K A X S sc) : ∀ (k : Nat) (r : MBarrier.Record Ref) (n tx : Nat),
      (X.objects S.full)[k]? = some r → r.fault = none → r.action = .arrive n tx →
      n = 1 ∧ ∃ x ∈ (SF X S).filter (fun x => x.1 ∈ ({⟨0, by omega⟩} : Finset (Kind S))),
        r.id = itF X S x.1 x.2 := by
  intro k r n tx hr hf ha
  have hrm := List.mem_of_getElem? hr
  obtain ⟨hn, -⟩ := arrival_source H hrm ha
  obtain ⟨x, hx, hid, hk⟩ := full_item H hrm hf (.inl ⟨n, tx, ha⟩)
  have hx0 : x.1 = ⟨0, by omega⟩ := Fin.ext (hk.mp ⟨n, tx, ha⟩)
  exact ⟨hn, x, Finset.mem_filter.mpr ⟨hx, by simp [hx0]⟩, hid⟩

/-- Every non-faulting arrival of the empty barrier is a unit notification. -/
theorem empty_count (H : Hyp L K A X S sc) : ∀ (k : Nat) (r : MBarrier.Record Ref)
    (n tx : Nat),
      (X.objects S.empty)[k]? = some r → r.fault = none →
      r.action = .arrive n tx → n = 1 ∧ ∃ y ∈ SE X S, r.id = note X S y.1 0 y.2 :=
  fun _ _ _ _ hr hf ha => empty_item H (List.mem_of_getElem? hr) hf ha

/-- **The consumer's poll for use `j`** found phase `j + 1` of the full barrier and observed
phase `j`. -/
theorem F_found (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) {b : Fin 1}
    {j : Nat}
    (hj : j < okPolls S.full (X.tr S.cm)) :
    ∃ i w st, (X.objects S.full)[i]? = some w ∧
      w.id = .thread (wF X S b j) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects S.full) i = some st ∧ st.phase = j + 1 ∧
      observedAt (X.objects S.full) i = some j ∧ oF X S b j = j := by
  obtain ⟨i, w, st, hi, hwid, hww, -, hsel, hcnt, hst, -, ho, hoF⟩ := F_poll hX H hj
  obtain ⟨st', hst', hph⟩ := (ring hX H hP).full_poll_phase hX (b := b)
    ({⟨0, by omega⟩} : Finset (Kind S)) (by simp) H.full_noInval
    (objectThreadSelected S.cm) (by decide : 0 ≤ 1) (F_alt hX H _)
    (fun k r n tx hr hf ha => by
      obtain ⟨hn, x, hx, hid⟩ := full_count H k r n tx hr hf ha
      exact ⟨hn, x, hx, hid⟩)
    (fun k st hs => by
      rw [Finset.card_singleton]
      exact PairTmaRing.expected_of_init hX H.full_init H.full_noInval hs)
    hi hwid hww hsel (by simpa using hcnt)
  rw [hst] at hst'
  cases hst'
  refine ⟨i, w, st, hi, hwid, hww, hst, hph, ?_, ?_⟩
  · rw [ho, hph, Nat.add_sub_cancel]
  · rw [hoF, hph, Nat.add_sub_cancel]

/-- **Producer `a`'s poll for use `n ≥ 1`** found phase `n` of the empty barrier and observed
phase `n - 1`. -/
theorem E_found (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) {a : Fin 2}
    {n : Nat}
    (hn : 1 ≤ n) (hj : n - S.δ < okPolls S.empty (X.tr (S.prod a))) :
    ∃ i w st, (X.objects S.empty)[i]? = some w ∧
      w.id = .thread (wE X S a n) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects S.empty) i = some st ∧ st.phase = n ∧
      observedAt (X.objects S.empty) i = some (n - 1) ∧
      oE X S a n = n - 1 := by
  have hδ := H.δ_le
  obtain ⟨i, w, st, hi, hwid, hww, -, hsel, hcnt, hst, -, ho, hoE⟩ := E_poll hX H hn hj
  obtain ⟨st', hst', hph⟩ := (ring hX H hP).empty_poll_phase hX Nat.one_pos
      (H.empty_noInval) (a := a)
    (objectThreadSelected (S.prod a)) (by omega : 1 - S.δ ≤ 1) (E_alt hX H _)
    (empty_count H) (fun k st hs => PairTmaRing.expected_of_init hX H.empty_init
    H.empty_noInval hs) hn hi hwid hww hsel (by rw [hcnt]; omega)
  rw [hst] at hst'
  cases hst'
  exact ⟨i, w, st, hi, hwid, hww, hst, hph, by rw [ho, hph], by rw [hoE, hph]⟩

/-- A counted item in the phase a consumer's poll observes is before it in the full barrier's
history, in that phase. -/
theorem F_update (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {b : Fin 1} {j : Nat}
    (hj : j < okPolls S.full (X.tr S.cm))
    {x : Kind S × Nat} (hx : x ∈ SF X S) (hph : phF X S x = oF X S b j) :
    UpdateBeforeWait (X.objects S.full) (itF X S x.1 x.2)
      (.thread (wF X S b j)) := by
  obtain ⟨iw, w, st, hiw, hwid, hww, hwf, -, -, -, -, hobs, hoF⟩ := F_poll hX H hj
  obtain ⟨⟨i, r, hi, hid, hf, h0, h1⟩, -⟩ := SF_op H hx
  obtain ⟨-, sd, hsd, -⟩ := PairTmaRing.state_of_init hX H.full_init H.full_noInval hi (by
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
  have h := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX _)
      H.full_noInval hi hf hiw hwf hww hp hobs
  rwa [hid, hwid] at h

/-- A counted notification in the phase a producer's poll observes is before it in the empty
barrier's history, in that phase. -/
theorem E_update (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n) (hj : n - S.δ < okPolls S.empty (X.tr (S.prod a)))
    {y : Fin 1 × Nat} (hy : y ∈ SE X S) (hph : phE X S y = oE X S a n) :
    UpdateBeforeWait (X.objects S.empty) (note X S y.1 a y.2) (.thread (wE X S a n)) := by
  obtain ⟨iw, w, st, hiw, hwid, hww, hwf, -, -, -, -, hobs, hoE⟩ := E_poll hX H hn hj
  obtain ⟨⟨i, r, hi, hid, hf, ha⟩, -⟩ := SE_op H hy
  obtain ⟨-, sd, hsd, -⟩ := PairTmaRing.state_of_init hX H.empty_init H.empty_noInval hi
    (by intro n; rw [ha]; simp)
  have hsd' : stateBefore (X.objects S.empty) i = some sd := hsd
  have hp : phaseAt (X.objects S.empty) i = some sd.phase := by
    simp [phaseAt, hsd']
  have hpo := MbarRing.Poll.phaseOf_eq hX hi hp
  unfold phE at hph
  rw [← hid, hpo, hoE] at hph
  rw [hph] at hp
  have h := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX _)
      H.empty_noInval hi hf hiw hwf hww hp hobs
  rwa [hid, hwid] at h

/-- **The items of use `j`.** The consumer's poll for use `j` observed every item of use `j`. -/
theorem consumer_observes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits)
    {b : Fin 1} {j : Nat}
    (hj : j < okPolls S.full (X.tr S.cm)) (k : Kind S) :
    (k, j) ∈ SF X S ∧ phF X S (k, j) = j ∧
      UpdateBeforeWait (X.objects S.full) (itF X S k j) (.thread (wF X S b j)) := by
  have hw : X.RefPresent (.thread (wF X S b j)) := MbarRing.Poll.nth_present.mpr hj
  obtain ⟨hx, hph⟩ := ((ring hX H hP).content_full hX.depAcyclic (b := b) hw).2 k
  obtain ⟨-, -, -, -, -, -, -, -, -, hoF⟩ := F_found hX H hP (b := b) hj
  have hph' : phF X S (k, j) = oF X S b j := hph
  exact ⟨hx, hph'.trans hoF, F_update hX H hj hx hph'⟩

/-- **The notifications of use `n`.** Producer `a`'s poll for use `n + 1` observed the consumer's
notification of use `n`. -/
theorem producer_observes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits)
    {a : Fin 2} {n : Nat}
    (hj : n + 1 - S.δ < okPolls S.empty (X.tr (S.prod a))) (b : Fin 1) :
    (b, n) ∈ SE X S ∧ phE X S (b, n) = n ∧
      UpdateBeforeWait (X.objects S.empty) (note X S b a n) (.thread (wE X S a (n + 1))) := by
  have hw : X.RefPresent (.thread (wE X S a (n + 1))) := MbarRing.Poll.nth_present.mpr hj
  obtain ⟨hy, hph⟩ := ((ring hX H hP).content_empty hX.depAcyclic (a := a) hw).2 b
  obtain ⟨-, -, -, -, -, -, -, -, -, hoE⟩ := E_found hX H hP (a := a) (by omega) hj
  have hph' : phE X S (b, n) = oE X S a (n + 1) := hph
  exact ⟨hy, by rw [hph', hoE]; rfl, E_update hX H (by omega) hj hy hph'⟩

end
end PTX.SingleTmaRing
