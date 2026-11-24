-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Attribution

@[expose] public section

/-! # What a pair TMA ring slot's attribution says

From the ring of items (`ring`) and the dependency order: consumer `b`'s poll for use `j` found
phase `j + 1` and observed phase `j` of the full barrier (`F_found`), holding every item of use `j`
(`consumer_observes`); producer `a`'s poll for use `n + 1` found phase `n + 1` of its empty
barrier and observed phase `n`, holding every consumer's notification of use `n`
(`producer_observes`). A counted item of use `u` lies in phase `u` or later (`use_le_phase`), so
the full barrier has at most `2 n` completions per phase reached (`completions_le`), and its
transaction counter stays within one use's bytes (`full_tx_bounds`). The uses of the items are
bounded by the pollers' successful polls (`SF_use_le`, `SE_use_lt`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {nc : Nat} {S : Slot nc}

theorem okPolls_take_le (m : Loc) (es : List Event) (k : Nat) :
    Flow.okPolls m (es.take k) ≤ Flow.okPolls m es := by
  unfold Flow.okPolls
  exact (List.take_sublist k es).countP_le

/-- Every non-faulting arrival of the full barrier is a unit arrival of a counted item of kind
`0`. -/
theorem full_count (H : Hyp L K A X S) : ∀ (k : Nat) (r : MBarrier.Record Ref) (n tx : Nat),
      (X.objects S.full)[k]? = some r → r.fault = none → r.action = .arrive n tx →
      n = 1 ∧ ∃ x ∈ (SF X S).filter (fun x => x.1 ∈ ({⟨0, by omega⟩} : Finset (Kind S.n))),
        r.id = itF X S x.1 x.2 := by
  intro k r n tx hr hf ha
  have hrm := List.mem_of_getElem? hr
  obtain ⟨hn, -⟩ := arrival_producer H hrm ha
  obtain ⟨x, hx, hid, hk⟩ := full_item H hrm hf (.inl ⟨n, tx, ha⟩)
  have hx0 : x.1 = ⟨0, by omega⟩ := Fin.ext (hk.mp ⟨n, tx, ha⟩)
  exact ⟨hn, x, Finset.mem_filter.mpr ⟨hx, by simp [hx0]⟩, hid⟩

/-- Every non-faulting arrival of an empty barrier is a unit notification. -/
theorem empty_count (H : Hyp L K A X S) {a : Fin 2} : ∀ (k : Nat) (r : MBarrier.Record Ref)
    (n tx : Nat),
      (X.objects (S.empty a))[k]? = some r → r.fault = none →
      r.action = .arrive n tx → n = 1 ∧ ∃ y ∈ SE X S a, r.id = note X S y.1 a y.2 :=
  fun _ _ _ _ hr hf ha => empty_item H (List.mem_of_getElem? hr) hf ha

/-- **Consumer `b`'s poll for use `j`** found phase `j + 1` of the full barrier and observed
phase `j`. -/
theorem F_found (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {j : Nat}
    (hj : j < okPolls S.full (X.tr (S.cons b))) :
    ∃ i w st, (X.objects S.full)[i]? = some w ∧
      w.id = .thread (wF X S b j) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects S.full) i = some st ∧ st.phase = j + 1 ∧
      observedAt (X.objects S.full) i = some j ∧ oF X S b j = j := by
  obtain ⟨i, w, st, hi, hwid, hww, -, hsel, hcnt, hst, -, ho, hoF⟩ := F_poll hX H hj
  obtain ⟨st', hst', hph⟩ := (ring hX H).full_poll_phase hX (b := b)
    ({⟨0, by omega⟩} : Finset (Kind S.n)) (by simp) H.full_noInval
    (objectThreadSelected (S.cons b)) (by decide : 0 ≤ 1) (F_alt hX H _)
    (fun k r n tx hr hf ha => by
      obtain ⟨hn, x, hx, hid⟩ := full_count H k r n tx hr hf ha
      exact ⟨hn, x, hx, hid⟩)
    (fun k st hs => by
      rw [Finset.card_singleton]; exact expected_of_init hX H.full_init H.full_noInval hs)
    hi hwid hww hsel (by simpa using hcnt)
  rw [hst] at hst'
  cases hst'
  refine ⟨i, w, st, hi, hwid, hww, hst, hph, ?_, ?_⟩
  · rw [ho, hph, Nat.add_sub_cancel]
  · rw [hoF, hph, Nat.add_sub_cancel]

/-- **Producer `a`'s poll for use `n ≥ 1`** found phase `n` of its empty barrier and observed
phase `n - 1`. -/
theorem E_found (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n)
    (hj : n < okPolls (S.empty a) (X.tr (S.prod a))) :
    ∃ i w st, (X.objects (S.empty a))[i]? = some w ∧
      w.id = .thread (wE X S a n) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects (S.empty a)) i = some st ∧ st.phase = n ∧
      observedAt (X.objects (S.empty a)) i = some (n - 1) ∧
      oE X S a n = n - 1 := by
  obtain ⟨i, w, st, hi, hwid, hww, -, hsel, hcnt, hst, -, ho, hoE⟩ := E_poll hX H hn hj
  obtain ⟨st', hst', hph⟩ := (ring hX H).empty_poll_phase hX H.nc_pos
      (H.empty_noInval a) (a := a)
    (objectThreadSelected (S.prod a)) (le_refl 1) (E_alt hX H _)
    (empty_count H) (fun k st hs => expected_of_init hX (H.empty_init a)
    (H.empty_noInval a) hs) hn hi hwid hww hsel (by rw [hcnt]; omega)
  rw [hst] at hst'
  cases hst'
  exact ⟨i, w, st, hi, hwid, hww, hst, hph, by rw [ho, hph], by rw [hoE, hph]⟩

/-- A counted item in the phase a consumer's poll observes is before it in the full barrier's
history, in that phase. -/
theorem F_update (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {j : Nat}
    (hj : j < okPolls S.full (X.tr (S.cons b)))
    {x : Kind S.n × Nat} (hx : x ∈ SF X S) (hph : phF X S x = oF X S b j) :
    UpdateBeforeWait (X.objects S.full) (itF X S x.1 x.2)
      (.thread (wF X S b j)) := by
  obtain ⟨iw, w, st, hiw, hwid, hww, hwf, -, -, -, -, hobs, hoF⟩ := F_poll hX H hj
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
  have h := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX _)
      H.full_noInval hi hf hiw hwf hww hp hobs
  rwa [hid, hwid] at h

/-- A counted notification in the phase a producer's poll observes is before it in the empty
barrier's history, in that phase. -/
theorem E_update (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n : Nat}
    (hn : 1 ≤ n)
    (hj : n < okPolls (S.empty a) (X.tr (S.prod a)))
    {y : Fin nc × Nat} (hy : y ∈ SE X S a) (hph : phE X S a y = oE X S a n) :
    UpdateBeforeWait (X.objects (S.empty a)) (note X S y.1 a y.2)
      (.thread (wE X S a n)) := by
  obtain ⟨iw, w, st, hiw, hwid, hww, hwf, -, -, -, -, hobs, hoE⟩ := E_poll hX H hn hj
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
  have h := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX _)
      (H.empty_noInval a) hi hf hiw hwf hww hp hobs
  rwa [hid, hwid] at h

/-- **The items of use `j`.** Consumer `b`'s poll for use `j` observed every item of use `j`. -/
theorem consumer_observes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {b : Fin nc} {j : Nat}
    (hj : j < okPolls S.full (X.tr (S.cons b))) (k : Kind S.n) :
    (k, j) ∈ SF X S ∧ phF X S (k, j) = j ∧
      UpdateBeforeWait (X.objects S.full) (itF X S k j)
        (.thread (wF X S b j)) := by
  have hw : X.RefPresent (.thread (wF X S b j)) := MbarRing.Poll.nth_present.mpr hj
  obtain ⟨hx, hph⟩ := ((ring hX H).content_full hX.depAcyclic (b := b) hw).2 k
  obtain ⟨-, -, -, -, -, -, -, -, -, hoF⟩ := F_found hX H hj
  have hph' : phF X S (k, j) = oF X S b j := hph
  exact ⟨hx, hph'.trans hoF, F_update hX H hj hx hph'⟩

/-- **The notifications of use `n`.** Producer `a`'s poll for use `n + 1` observed consumer
`b`'s notification of use `n`. -/
theorem producer_observes (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {n : Nat}
    (hj : n + 1 < okPolls (S.empty a) (X.tr (S.prod a))) (b : Fin nc) :
    (b, n) ∈ SE X S a ∧ phE X S a (b, n) = n ∧
      UpdateBeforeWait (X.objects (S.empty a)) (note X S b a n)
        (.thread (wE X S a (n + 1))) := by
  have hw : X.RefPresent (.thread (wE X S a (n + 1))) := MbarRing.Poll.nth_present.mpr hj
  obtain ⟨hy, hph⟩ := ((ring hX H).content_empty hX.depAcyclic (a := a) hw).2 b
  obtain ⟨-, -, -, -, -, -, -, -, -, hoE⟩ := E_found hX H (by omega) hj
  have hph' : phE X S a (b, n) = oE X S a (n + 1) := hph
  exact ⟨hy, by rw [hph', hoE]; rfl, E_update hX H (by omega) hj hy hph'⟩

/-! ### Uses -/

/-- A counted item's use is below its producer's successful empty polls. -/
theorem SF_use_lt (H : Hyp L K A X S) {x : Kind S.n × Nat} (hx : x ∈ SF X S) :
    x.2 + 1 ≤ okPolls (S.empty (kOwner S.n x.1)) (X.tr (S.prod (kOwner S.n x.1))) :=
  (SF_op H hx).2.2.trans (okPolls_take_le _ _ _)

/-- A counted notification's use is below its consumer's successful full polls. -/
theorem SE_use_lt_F (H : Hyp L K A X S) {a : Fin 2} {y : Fin nc × Nat}
    (hy : y ∈ SE X S a) :
    y.2 + 1 ≤ okPolls S.full (X.tr (S.cons y.1)) :=
  (SE_op H hy).2.2.trans (okPolls_take_le _ _ _)

/-- A counted notification's use is below every producer's successful empty polls: the
consumer's poll of its use observed the producer's items of that use. -/
theorem SE_use_lt (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} {y : Fin nc × Nat}
    (hy : y ∈ SE X S a) (a' : Fin 2) :
    y.2 + 1 ≤ okPolls (S.empty a') (X.tr (S.prod a')) := by
  obtain ⟨hx, -⟩ := consumer_observes hX H (SE_use_lt_F H hy) (copyKind S.n a' 0
    H.n_pos)
  have h := SF_use_lt H hx
  rwa [kOwner_copyKind] at h

/-- A counted item of use `u ≥ 1` follows every consumer's poll for use `u - 1`. -/
theorem SF_reach (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {x : Kind S.n × Nat}
    (hx : x ∈ SF X S)
    (b : Fin nc) {j : Nat} (hj : j < x.2) :
    X.RefPresent (.thread (wF X S b j)) ∧
      Relation.TransGen (DepStep L K X) (.thread (wF X S b j), true)
        (itF X S x.1 x.2, false) := by
  obtain ⟨hp, hpath⟩ := (ring hX H).reach_op hX.depAcyclic (a := kOwner S.n x.1)
    (s := x.2) (op := opF X S x.1 x.2) (fun n _ hn => guardP H hx hn) b hj
  exact ⟨hp, hpath.trans_left (issueF hX H hx)⟩

/-- A counted item's use is at most every consumer's successful full polls. -/
theorem SF_use_le (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {x : Kind S.n × Nat}
    (hx : x ∈ SF X S)
    (b : Fin nc) : x.2 ≤ okPolls S.full (X.tr (S.cons b)) := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  · have := MbarRing.Poll.nth_present.mp (SF_reach hX H hx b (j := x.2 - 1) (by omega)).1
    omega

/-- **An item lies in its use's phase or later.** -/
theorem use_le_phase (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {x : Kind S.n × Nat}
    (hx : x ∈ SF X S)
    {i : Nat} {r : Record Ref} (hi : (X.objects S.full)[i]? = some r)
    (hid : r.id = itF X S x.1 x.2) {st : State}
    (hst : stateBefore (X.objects S.full) i = some st) : x.2 ≤ st.phase := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  have hch := X.objects_checked hX S.full
  have hni := H.full_noInval
  obtain ⟨hp, hpath⟩ := SF_reach hX H hx ⟨0, H.nc_pos⟩ (j := x.2 - 1) (by omega)
  obtain ⟨k, w, sk, hk, hwid, hww, hsk, hskp, -⟩ :=
    F_found hX H (MbarRing.Poll.nth_present.mp hp)
  have hnb := MbarRing.Round.Slot.not_before_of_reach (m := S.full) hX hpath
  -- the item's record is not a poll
  obtain ⟨⟨i', r', hi', hid', -, h0, h1⟩, -⟩ := SF_op H hx
  have hii := ObjectInit.checked_record_index_eq hch hi hi' (hid.trans hid'.symm)
  subst hii
  rw [hi] at hi'
  cases hi'
  have hki : k < i := by
    rcases Nat.lt_trichotomy k i with h | rfl | h
    · exact h
    · rw [hi] at hk
      cases hk
      obtain ⟨-, p, -, hact, -⟩ := hch.okPoll hi hww
      by_cases hk0 : x.1.val = 0
      · rw [h0 hk0] at hact; cases hact
      · rw [h1 hk0] at hact; cases hact
    · exact absurd ⟨i, k, r, w, hi, hid, hk, hwid, h⟩ hnb
  have hil : i ≤ (X.objects S.full).length :=
    (List.getElem?_eq_some_iff.mp hi).1.le
  obtain ⟨t, ht', hle⟩ := hch.phase_mono hni hki.le hil hsk
  rw [hst] at ht'
  cases ht'
  omega

/-! ### The full barrier's transactions -/

/-- The fault-free completions of the full barrier before a position are at most `2 n` per
phase reached. -/
theorem completions_le (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {j : Nat}
    (hj : j ≤ (X.objects S.full).length) {st : State}
    (hst : stateBefore (X.objects S.full) j = some st) :
    completedTxCount ((X.objects S.full).take j) ≤ 2 * S.n * (st.phase + 1) := by
  classical
  set log := X.objects S.full with hlog
  have hch : CheckedLog log := X.objects_checked hX S.full
  have hni := H.full_noInval
  let pred : Record Ref → Bool := fun r =>
    match r.action, r.fault with | .completeTx _, none => true | _, _ => false
  have hpred : ∀ r, pred r = true ↔ (∃ n, r.action = .completeTx n) ∧ r.fault = none := by
    intro r
    simp only [pred]
    cases r.action <;> cases r.fault <;> simp
  have hcnt : completedTxCount (log.take j) = (log.take j).countP pred := rfl
  rw [hcnt, MbarRing.Slot.countP_take_card]
  let T := (Finset.univ.filter (fun k : Kind S.n => k.val ≠ 0)) ×ˢ Finset.range (st.phase + 1)
  have hT : T.card = 2 * S.n * (st.phase + 1) := by
    have h0 : Finset.univ.filter (fun k : Kind S.n => k.val ≠ 0) =
        Finset.univ.erase ⟨0, by omega⟩ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true, ne_eq,
        Fin.ext_iff]
    rw [Finset.card_product, Finset.card_range, h0, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  rw [← hT]
  refine PairTmaRing.card_le_of_rel _ T (fun k x => ∃ r, log[k]? = some r ∧ r.id = itF X S x.1 x.2)
    (fun k hk => ?_) (fun k hk k' hk' x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨hkj, hpk⟩ := Finset.mem_filter.mp hk
  have hkj' := Finset.mem_range.mp hkj
  obtain ⟨r, hr⟩ : ∃ r, log[k]? = some r := by
    cases h : log[k]? with
    | none => rw [h] at hpk; simp at hpk
    | some r => exact ⟨r, rfl⟩
  rw [hr] at hpk
  obtain ⟨⟨n, ha⟩, hf⟩ := (hpred r).mp hpk
  obtain ⟨x, hx, hid, hk0⟩ := full_item H (List.mem_of_getElem? hr) hf (.inr ⟨n, ha⟩)
  have hx0 : x.1.val ≠ 0 := fun h => by
    obtain ⟨n', tx', ha'⟩ := hk0.mpr h
    rw [ha] at ha'; cases ha'
  obtain ⟨-, sk, hsk, -⟩ := state_of_init hX H.full_init H.full_noInval hr
      (by intro n'; rw [ha]; simp)
  have hle := use_le_phase hX H hx hr hid hsk
  obtain ⟨t, ht', hph⟩ := hch.phase_mono hni hkj'.le hj hsk
  rw [hst] at ht'
  cases ht'
  refine ⟨x, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩,
    Finset.mem_range.mpr (by omega)⟩, r, hr, hid⟩

/-- The full barrier's expected bytes are one use's per arrival unit. -/
theorem full_expected_bytes (H : Hyp L K A X S) :
    ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects S.full) →
      expectedTxBytes xs = S.tx * arrivalUnits xs := by
  intro xs hxs
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    have hr := hxs r List.mem_cons_self
    rw [expectedTxBytes, arrivalUnits, ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))]
    unfold Record.expectedTxBytes
    cases ha : r.action with
    | arrive n tx =>
      obtain ⟨rfl, rfl, -⟩ := arrival_producer H hr ha
      cases r.fault
      · simp only; ring
      · simp
    | _ => cases r.fault <;> simp

/-- The full barrier's completed bytes are one copy per completion. -/
theorem full_uniform (H : Hyp L K A X S) : ∀ q ∈ X.objects S.full, ∀ n, q.action = .completeTx n →
      q.fault = none → n = S.bytes :=
  fun _ hq _ hn _ => (completion_producer H hq hn).1

/-- **The full barrier's transaction counter** stays within one use's bytes. -/
theorem full_tx_bounds (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {j : Nat}
    (hj : j ≤ (X.objects S.full).length) {st : State}
    (hst : stateBefore (X.objects S.full) j = some st) :
    -S.tx ≤ st.tx ∧ st.tx ≤ S.tx := by
  classical
  set log := X.objects S.full with hlog
  have hch : CheckedLog log := X.objects_checked hX S.full
  have hni := H.full_noInval
  have hexp := expected_of_init hX H.full_init H.full_noInval hst
  constructor
  · -- by the totals: a use's bytes per arrival unit, a copy per completion
    have hbal := hch.tx_balance hni hj hst
    have he := full_expected_bytes H (log.take j) (fun q hq => List.mem_of_mem_take hq)
    have hu : UniformCompletedTx (log.take j) S.bytes := fun q hq hf n hn =>
      full_uniform H q (List.mem_of_mem_take hq) n hn hf
    have hc := completedTxBytes_eq_unit_mul_count hu
    obtain ⟨-, hacc⟩ := (hch.accounted hni hj).2 st hst
    have hcl := completions_le hX H hj hst
    simp only [unitsBefore] at hacc
    rw [he, hc] at hbal
    rw [hexp] at hacc
    have : (st.phase : Int) ≤ (arrivalUnits (log.take j) : Int) := by
      have : st.phase ≤ arrivalUnits (log.take j) := by
        have := (hch.accounted hni hj).2 st hst
        rw [hexp] at this
        omega
      exact_mod_cast this
    have hcl' : ((completedTxCount (log.take j) : Nat) : Int) ≤ 2 * S.n *
    ((st.phase : Int) + 1) := by
      exact_mod_cast hcl
    have htx : (S.tx : Int) = 2 * S.n * S.bytes := by simp [Slot.tx]
    have h1 : (S.bytes : Int) * (completedTxCount (log.take j) : Nat) ≤
        S.bytes * (2 * S.n * ((st.phase : Int) + 1)) :=
      mul_le_mul_of_nonneg_left hcl' (by positivity)
    have h2 : (S.tx : Int) * ((st.phase : Int) + 1) ≤ S.tx * ((arrivalUnits
    (log.take j) : Int) + 1) :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    rw [hbal]
    push_cast
    rw [htx] at h2 ⊢
    nlinarith
  · -- by the current phase: no more than one arrival unit
    have htx := hch.tx_eq hni hj hst
    have hpe := hch.pending_eq hni hj hst
    rw [hexp, phaseIncrements_eq_zero (fun r hr hi => by
      cases H.full_src r hr with
      | init ha | poll _ _ ha | arrive _ _ ha _ | copy _ _ _ ha => rw [hi] at ha; cases ha)]
      at hpe
    have hle : phaseTx log j st.phase ≤ S.tx * (phaseUnits log j st.phase : Int) := by
      unfold phaseTx phaseUnits
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k hk => ?_)
      split_ifs
      · unfold txDeltaAt unitsAt
        cases hr : log[k]? with
        | none => simp
        | some r =>
          simp only
          unfold Record.txDelta
          by_cases hf : r.fault = none
          · rw [ite_eq_left hf, ite_eq_left hf]
            cases ha : r.action with
            | arrive n tx =>
              obtain ⟨rfl, rfl, -⟩ := arrival_producer H (List.mem_of_getElem? hr) ha
              simp [Action.txDelta, Action.units]
            | completeTx n => simp [Action.txDelta, Action.units]
            | init n => simp [Action.txDelta, Action.units]
            | pollParity p ok => simp [Action.txDelta, Action.units]
            | inval => exact (hni r (List.mem_of_getElem? hr) ha).elim
            | increment => simp [Action.txDelta, Action.units]
          · rw [ite_eq_right hf, ite_eq_right hf]; simp
      · simp
    have : (phaseUnits log j st.phase : Int) ≤ 1 := by exact_mod_cast (by omega : _ ≤ 1)
    have h1 := mul_le_mul_of_nonneg_left this (by positivity : (0 : Int) ≤ S.tx)
    omega

end
end PTX.PairTmaRing
