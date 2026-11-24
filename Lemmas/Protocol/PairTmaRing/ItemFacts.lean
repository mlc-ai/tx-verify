-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Items

@[expose] public section

/-! # The facts of a pair TMA ring slot's items and polls

A proof tool. An object initialized first (`InitFirst`) and never invalidated has, at every
other record, a state with the initialization's count (`state_of_init`, `expected_of_init`),
and its initialization and poll records do not fault (`init_clean`, `poll_clean`). Under
`Hyp`: a counted item's event is its producer's event of its kind with the item's count of
earlier ones, after more successful polls of the producer's empty barrier than its use
(`SF_op`); a counted notification's commit likewise after more successful full polls of its
consumer than its use (`SE_op`). The producers' and consumers' successful polls alternate
parity on their barriers (`F_alt`, `E_alt`) and observe a completed phase (`F_poll`,
`E_poll`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-! ### Objects initialized first -/

section
variable {m : Loc} {c : Nat}

/-- An object's records other than its initialization find a state, with the initialization's
count. -/
theorem state_of_init (hX : Consistent L K A mem0 X) (hfirst : InitFirst X m c)
    (hni : NoInval (X.objects m)) {i : Nat} {r : Record Ref} (hi : (X.objects m)[i]? = some r)
    (hnon : ∀ n, r.action ≠ .init n) :
    0 < i ∧ ∃ st, stateBefore (X.objects m) i = some st ∧ st.expected = c := by
  have hch := X.objects_checked hX m
  obtain ⟨r0, h0, ha0, hf0, -⟩ := hfirst r (List.mem_of_getElem? hi)
  have hpos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h0] at hi; cases hi; exact absurd ha0 (hnon _)
    · exact hpos
  have hlt : i < (X.objects m).length := (List.getElem?_eq_some_iff.mp hi).1
  exact ⟨hpos, ObjectInit.checked_expected_after_init hch hni h0 ha0 hf0 hpos hlt.le⟩

/-- Every state of an object initialized first has the initialization's count. -/
theorem expected_of_init (hX : Consistent L K A mem0 X) (hfirst : InitFirst X m c)
    (hni : NoInval (X.objects m)) {k : Nat} {st : State}
    (hs : stateBefore (X.objects m) k = some st) : st.expected = c := by
  have hch := X.objects_checked hX m
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp [stateBefore] at hs
    · exact h
  obtain ⟨r, hr⟩ : ∃ r, (X.objects m)[k - 1]? = some r := by
    simp only [stateBefore, show k ≠ 0 by omega, ↓reduceIte] at hs
    cases h : (X.objects m)[k - 1]? with
    | none => rw [h] at hs; cases hs
    | some r => exact ⟨r, rfl⟩
  obtain ⟨r0, h0, ha0, hf0, -⟩ := hfirst r (List.mem_of_getElem? hr)
  have hlt : k - 1 < (X.objects m).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨st', hs', he⟩ := ObjectInit.checked_expected_after_init hch hni h0 ha0 hf0 hk (by omega)
  rw [hs] at hs'
  cases hs'
  exact he

/-- An object's initialization records do not fault: there is one, its first record. -/
theorem init_clean (hfirst : InitFirst X m c) {q : Record Ref} (hq : q ∈ X.objects m) {n : Nat}
    (ha : q.action = .init n) : q.fault = none := by
  obtain ⟨r0, -, -, hf0, hone⟩ := hfirst q hq
  rw [hone q hq ⟨n, ha⟩]
  exact hf0

/-- An object's polls do not fault: they find the state of its initialization. -/
theorem poll_clean (hX : Consistent L K A mem0 X) (hfirst : InitFirst X m c)
    (hni : NoInval (X.objects m)) :
    ∀ q ∈ X.objects m, (∃ p ok, q.action = .pollParity p ok) → q.fault = none := by
  intro q hq ⟨p, ok, ha⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  obtain ⟨-, st, hst, -⟩ := state_of_init hX hfirst hni hi (by intro n; rw [ha]; simp)
  have hok := (X.objects_checked hX _).at hi
  rw [hst] at hok
  unfold RecordOk at hok
  rw [ha] at hok
  simp only [perform, pure, Except.pure] at hok
  exact hok.2

end

variable {nc : Nat} {S : Slot nc}

theorem full_poll_clean (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) :
    ∀ q ∈ X.objects S.full, (∃ p ok, q.action = .pollParity p ok) → q.fault = none :=
  poll_clean hX H.full_init H.full_noInval

theorem empty_poll_clean (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} :
    ∀ q ∈ X.objects (S.empty a), (∃ p ok, q.action = .pollParity p ok) → q.fault = none :=
  poll_clean hX (H.empty_init a) (H.empty_noInval a)

/-! ### The items' events -/

/-- The record of a counted item, and its producer's event: the event of its kind with the
item's count of earlier ones, after more successful polls of the producer's empty barrier than
the item's use. -/
theorem SF_op (H : Hyp L K A X S) {x : Kind S.n × Nat} (hx : x ∈ SF X S) :
    (∃ (i : Nat) (r : Record Ref), (X.objects S.full)[i]? = some r ∧ r.id = itF X S x.1 x.2 ∧
      r.fault = none ∧ (x.1.val = 0 → r.action = .arrive 1 S.tx) ∧
      (x.1.val ≠ 0 → r.action = .completeTx S.bytes)) ∧
    (∃ e, X.get (opF X S x.1 x.2) = some e ∧ kPred S x.1 e = true ∧
      ((X.tr (S.prod (kOwner S.n x.1))).take (opF X S x.1 x.2).2).countP (kPred S x.1) =
        kIdx S.n x.1 x.2) ∧
    x.2 + 1 ≤ okPolls (S.empty (kOwner S.n x.1))
      ((X.tr (S.prod (kOwner S.n x.1))).take (opF X S x.1 x.2).2) := by
  obtain ⟨-, r, hr, hid, hf, h0, h1⟩ := Finset.mem_filter.mp hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  refine ⟨⟨i, r, hi, hid, hf, h0, h1⟩, ?_⟩
  by_cases hk : x.1.val = 0
  · have hk0 : x.1 = ⟨0, by omega⟩ := Fin.ext hk
    obtain ⟨-, -, j, pc, rel, sc, hid', he, hab⟩ := arrival_producer H hr (h0 hk)
    rw [hk0] at hid ⊢
    rw [itF_zero, hid'] at hid
    simp only [Ref.thread.injEq, Prod.mk.injEq, true_and] at hid
    rw [opF_zero]
    simp only
    rw [← hid]
    have hp : arrivesOn S.full ⟨pc, .arrive S.full S.tx 1 rel sc⟩ = true := by
      simp [arrivesOn, sourceArrive]
    have hcnt := (nthEv_spec_of_get (hid ▸ he)).2
    rw [← hid] at hcnt
    have hko : kOwner S.n ⟨0, by omega⟩ = 0 := by simp [kOwner]
    rw [hko, kPred_zero]
    refine ⟨⟨_, he, hp, hcnt⟩, ?_⟩
    unfold arrivals at hab
    rw [hcnt] at hab
    simpa [kIdx] using hab
  · obtain ⟨-, a, j, pc, al, sp, hid', he, hm, hib⟩ := completion_producer H hr (h1 hk)
    rw [itF_ne hk, hid'] at hid
    simp only [Ref.async.injEq, Prod.mk.injEq, and_true] at hid
    obtain ⟨hpa, hj⟩ := hid
    have ha := H.prod_inj hpa
    subst ha
    rw [opF_ne hk]
    simp only
    rw [← hj, kPred_ne hk]
    have hp : issuesTo S.full ⟨pc, .tensorIssue al sp⟩ = true := by simp [issuesTo, hm]
    have hcnt := (nthEv_spec_of_get (hj ▸ he)).2
    rw [← hj] at hcnt
    refine ⟨⟨_, he, hp, hcnt⟩, ?_⟩
    rw [hcnt] at hib
    unfold kIdx at hib
    simp only [hk, ↓reduceIte] at hib
    exact Nat.lt_of_mul_lt_mul_left (a := S.n) (by omega)

/-- The record of a counted notification, and its consumer's commit: the commit with the use's
count of earlier ones, after more successful full polls of the consumer than the use. -/
theorem SE_op (H : Hyp L K A X S) {a : Fin 2} {y : Fin nc × Nat} (hy : y ∈ SE X S a) :
    (∃ (i : Nat) (r : Record Ref), (X.objects (S.empty a))[i]? = some r ∧
      r.id = note X S y.1 a y.2 ∧ r.fault = none ∧ r.action = .arrive 1 0) ∧
    (∃ pc sp, X.get (cm X S y.1 y.2) = some ⟨pc, .tc (.commit sp)⟩ ∧ sp.mbar = S.empty 0 ∧
      TcCommit.target sp (rankOf a) = some (S.empty a) ∧
      ((X.tr (S.cons y.1)).take (cm X S y.1 y.2).2).countP (commitsTo (S.empty 0)) = y.2) ∧
    y.2 + 1 ≤ okPolls S.full ((X.tr (S.cons y.1)).take (cm X S y.1 y.2).2) := by
  obtain ⟨-, r, hr, hid, hf, ha⟩ := Finset.mem_filter.mp hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  refine ⟨⟨i, r, hi, hid, hf, ha⟩, ?_⟩
  obtain ⟨-, -, b, j, pc, sp, hid', he, hm, htg, hcb⟩ := notify_consumer H hr ha
  rw [hid'] at hid
  simp only [note, cm, Ref.async.injEq, Prod.mk.injEq, and_true] at hid
  obtain ⟨hb, hj⟩ := hid
  have hb' := H.cons_inj hb
  subst hb'
  have hp : commitsTo (S.empty 0) ⟨pc, .tc (.commit sp)⟩ = true := by simp [commitsTo, hm]
  have hcnt := (nthEv_spec_of_get (hj ▸ he)).2
  rw [← hj] at hcnt
  simp only [cm]
  rw [← hj]
  refine ⟨⟨pc, sp, he, hm, htg, hcnt⟩, ?_⟩
  rw [hcnt] at hcb
  exact hcb

/-! ### Polls -/

theorem F_alt (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (g : Nat) :
    SelectedAlternates (objectThreadSelected g) (X.objects S.full) 0 :=
  MbarRing.Poll.alternates hX (full_poll_clean hX H) fun _ _ _ _ _ he => H.full_parity he

theorem E_alt (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} (g : Nat) :
    SelectedAlternates (objectThreadSelected g) (X.objects (S.empty a)) 1 :=
  MbarRing.Poll.alternates hX (empty_poll_clean hX H) fun _ _ _ _ _ he => H.empty_parity he

/-- Consumer `b`'s successful full poll with `j` earlier ones: its record, which found a state
past phase `0` and observed the phase before it, `oF b j`. -/
theorem F_poll (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {j : Nat}
    (hj : j < okPolls S.full (X.tr (S.cons b))) :
    ∃ i w st, (X.objects S.full)[i]? = some w ∧ w.id = .thread (wF X S b j) ∧
      w.reply.waited = some true ∧ w.fault = none ∧
      objectThreadSelected (S.cons b) w.id = true ∧
      selectedBefore (objectThreadSelected (S.cons b)) (X.objects S.full) i = j ∧
      stateBefore (X.objects S.full) i = some st ∧ 0 < st.phase ∧
      observedAt (X.objects S.full) i = some (st.phase - 1) ∧ oF X S b j = st.phase - 1 := by
  obtain ⟨i, w, p, hi, hwid, -, hww, hwf, hsel⟩ :=
    MbarRing.Poll.record hX (full_poll_clean hX H) hj
  have hs : objectThreadSelected (S.cons b) w.id = true :=
    objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
    H.full_noInval (by decide : 0 ≤ 1) (F_alt hX H _) hi hs hww (by omega)
  refine ⟨i, w, st, hi, hwid, hww, hwf, hs, hsel, hst, hpos, ho, ?_⟩
  unfold oF wF
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hi ho

/-- Producer `a`'s successful empty poll with `n ≥ 1` earlier ones: its record, which found a
state past phase `0` and observed the phase before it, `oE a n`. -/
theorem E_poll (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n) (hj : n < okPolls (S.empty a) (X.tr (S.prod a))) :
    ∃ i w st, (X.objects (S.empty a))[i]? = some w ∧ w.id = .thread (wE X S a n) ∧
      w.reply.waited = some true ∧ w.fault = none ∧
      objectThreadSelected (S.prod a) w.id = true ∧
      selectedBefore (objectThreadSelected (S.prod a)) (X.objects (S.empty a)) i = n ∧
      stateBefore (X.objects (S.empty a)) i = some st ∧ 0 < st.phase ∧
      observedAt (X.objects (S.empty a)) i = some (st.phase - 1) ∧
      oE X S a n = st.phase - 1 := by
  obtain ⟨i, w, p, hi, hwid, -, hww, hwf, hsel⟩ :=
    MbarRing.Poll.record hX (empty_poll_clean hX H) hj
  have hs : objectThreadSelected (S.prod a) w.id = true :=
    objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (X.objects_checked hX _)
    (H.empty_noInval a) (le_refl _) (E_alt hX H _) hi hs hww (by omega)
  refine ⟨i, w, st, hi, hwid, hww, hwf, hs, hsel, hst, hpos, ho, ?_⟩
  unfold oE wE
  rw [← hwid]
  exact MbarRing.Poll.observedOf_eq hX hi ho

end
end PTX.PairTmaRing
