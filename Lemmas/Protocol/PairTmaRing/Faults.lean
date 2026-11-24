-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.RingFacts
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # A pair TMA ring slot's records are fault-free

A proof tool. Under `Hyp`, every record of a slot's barriers is fault-free (`fault_free`). The
initialization is the barrier's first record and only one; polls find its state (`init_clean`,
`poll_clean`). A completion of the full barrier keeps its transaction counter within range
(`full_tx_bounds`). An arrival, of the full barrier by the leader producer or of an empty barrier
by a consumer's commit, carries valid operands and keeps the counter in range; it neither
underflows nor arrives in an unobserved phase (`MBarrier.CheckedLog.arrive_fault_free`): were it
faulting, its item would not be counted, so no counted item of its kind has a later use
(a later use needs a poll that observed it), which bounds the arrival units before it; and the
pollers' polls for the earlier uses precede it in the barrier's history (they precede it in
the dependency order), where they found the phases up to its use (`F_found`, `E_found`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

/-- An arrival with valid operands that keeps the transaction counter in range faults only by
arriving in an unobserved phase or by underflowing the pending count. -/
theorem arrive_fault_cases {ι : Type} {st : State} {r : Record ι} {n tx : Nat}
    (hr : RecordOk (some st) r) (ha : r.action = .arrive n tx) (hn : validCount n)
    (htx : validTxOperand tx) (hv : validTx (st.tx + tx)) :
    r.fault = none ∨ r.fault = some .precedingPhaseNotObserved ∨
      r.fault = some .arrivalUnderflow := by
  unfold RecordOk at hr
  rw [ha] at hr
  simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hr
  split_ifs at hr
  all_goals simp_all

/-- A completion of valid size that keeps the transaction counter in range does not fault. -/
theorem complete_fault_free {ι : Type} {st : State} {r : Record ι} {n : Nat}
    (hr : RecordOk (some st) r) (ha : r.action = .completeTx n) (hn : validTxOperand n)
    (hv : validTx (st.tx - n)) : r.fault = none := by
  unfold RecordOk at hr
  rw [ha] at hr
  simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hr
  split_ifs at hr
  simp_all

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {nc : Nat} {S : Slot nc}

/-- An empty barrier's transaction counter is zero: only unit notifications arrive on it, and
nothing completes on it. -/
theorem empty_tx_zero (hX : Consistent L K A mem0 X) (H : Hyp L K A X S)
    {a : Fin 2} {j : Nat} (hj : j ≤ (X.objects (S.empty a)).length)
    {st : State} (hst : stateBefore (X.objects (S.empty a)) j = some st) :
    st.tx = 0 := by
  have hbal := (X.objects_checked hX _).tx_balance (H.empty_noInval a) hj hst
  have hz : ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects (S.empty a)) →
      expectedTxBytes xs = 0 ∧ completedTxBytes xs = 0 := by
    intro xs hxs
    induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons r rest ih =>
      have hr := hxs r List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))
      rw [expectedTxBytes, completedTxBytes, h1, h2]
      unfold Record.expectedTxBytes Record.completedTxBytes
      cases ha : r.action with
      | arrive n tx =>
        obtain ⟨-, rfl, -⟩ := notify_consumer H hr ha
        cases r.fault <;> simp
      | completeTx n =>
        exfalso
        cases H.empty_src a r hr with
        | init ha' => rw [ha] at ha'; cases ha'
        | poll _ _ ha' => rw [ha] at ha'; cases ha'
        | notify _ _ _ _ ha' => rw [ha] at ha'; cases ha'
      | _ => cases r.fault <;> simp
  obtain ⟨h1, h2⟩ := hz _ (fun q hq => List.mem_of_mem_take hq)
  rw [hbal, h1, h2]
  rfl

/-- **Fault freedom of the full barrier.** -/
theorem full_fault_free (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) :
    ∀ r ∈ X.objects (S.full), r.fault = none := by
  classical
  intro r hr
  set log := X.objects (S.full) with hlog
  have hch : CheckedLog log := X.objects_checked hX (S.full)
  have hni := H.full_noInval
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hil : i ≤ log.length := (List.getElem?_eq_some_iff.mp hi).1.le
  cases ha : r.action with
  | inval => exact (hni r hr ha).elim
  | increment =>
    exfalso
    cases H.full_src r hr with
    | init ha' | poll _ _ ha' | arrive _ _ ha' _ | copy _ _ _ ha' => rw [ha] at ha'; cases ha'
  | init n =>
    exact init_clean H.full_init hr ha
  | pollParity p ok => exact full_poll_clean hX H r hr ⟨p, ok, ha⟩
  | completeTx n =>
    obtain ⟨rfl, -⟩ := completion_producer H hr ha
    obtain ⟨-, st, hst, -⟩ := state_of_init hX H.full_init H.full_noInval hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    obtain ⟨hlo, hhi⟩ := full_tx_bounds hX H hil hst'
    have hbt := H.bytes_le_tx
    have hl := H.tx_le
    unfold limit at hl
    have hok := hch.at hi
    rw [hst'] at hok
    exact complete_fault_free hok ha (by unfold validTxOperand; omega)
      (by unfold validTx limit; omega)
  | arrive n tx =>
    obtain ⟨rfl, rfl, j, pc, rel, sc, hid, he, hab⟩ := arrival_producer H hr ha
    obtain ⟨-, st, hst, -⟩ := state_of_init hX H.full_init H.full_noInval hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    obtain ⟨hlo, hhi⟩ := full_tx_bounds hX H hil hst'
    have hbt := H.bytes_le_tx
    have hl := H.tx_le
    unfold limit at hl
    have hok := hch.at hi
    rw [hst'] at hok
    rcases arrive_fault_cases hok ha (by unfold validCount limit; omega)
      (by unfold validTxOperand; omega) (by unfold validTx limit; omega) with h | h | h
    · exact h
    all_goals
      exfalso
      have hf : r.fault ≠ none := by rw [h]; simp
      set u := arrivals (S.full) ((X.tr (S.prod 0)).take j) with hu
      have hp : arrivesOn (S.full)
          ⟨pc, .arrive (S.full) S.tx 1 rel sc⟩ = true := by
        simp [arrivesOn, sourceArrive]
      have hit : itF X S ⟨0, by omega⟩ u = r.id := by
        rw [itF_zero, hid, hu]
        unfold arrivals
        rw [nthEv_eq he hp]
      -- the arrival is not counted, so no counted arrival has a later use
      have hnot : (⟨0, by omega⟩, u) ∉ SF X S := by
        intro hx
        obtain ⟨-, r', hr', hid', hf', -⟩ := Finset.mem_filter.mp hx
        rw [hX.record_eq hr' hr (hid'.trans hit)] at hf'
        exact hf hf'
      have hle : ∀ x ∈ SF X S, x.2 ≤ u := by
        intro x hx
        by_contra hgt
        obtain ⟨hp', -⟩ := SF_reach hX H hx ⟨0, H.nc_pos⟩ (j := u) (by omega)
        exact hnot (consumer_observes hX H (MbarRing.Poll.nth_present.mp hp') ⟨0, by omega⟩).1
      have hunits : unitsBefore log i ≤ u := by
        have h := MbarRing.Round.units_le_of_uses hch (fun y : Unit × Nat => itF X S
        ⟨0, by omega⟩ y.2)
          (Finset.univ ×ˢ Finset.range u) (i := i)
          (fun k r c' tx hr hf ha => (full_count H k r c' tx hr hf ha).1)
          (fun k _ r' c' tx hr' hf' ha' => by
            obtain ⟨-, x, hx, hid'⟩ := full_count H k r' c' tx hr' hf' ha'
            obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
            have hx0' : x.1 = ⟨0, by omega⟩ := by simpa using hx0
            have hxu : x.2 ≠ u := fun h => hnot (by rw [← hx0', ← h]; exact hxS)
            refine ⟨((), x.2), Finset.mem_product.mpr ⟨Finset.mem_univ _,
              Finset.mem_range.mpr (by have := hle x hxS; omega)⟩, ?_⟩
            rw [hid', hx0'])
        simpa using h
      have hguard : ∀ n, 1 ≤ n → n ≤ u → Resumes K X
          ((ring hX H).wE 0 n) (S.prod 0, j) := fun n _ hn =>
        MbarRing.Poll.guard H.spins (len_of_get he) (by omega)
      have hff := hch.arrive_fault_free hni (s := u) hi ha
        (fun st' hs => by
          rw [expected_of_init hX H.full_init H.full_noInval hs]
          omega)
        (fun q hq1 hqu => by
          obtain ⟨hpw, hpath⟩ := (ring hX H).reach_op hX.depAcyclic hguard
            ⟨0, H.nc_pos⟩ (j := q - 1) (by omega)
          obtain ⟨k, w, sk, hk, hwid, hww, hsk, hskp, -⟩ :=
            F_found hX H (MbarRing.Poll.nth_present.mp hpw)
          have hnb := MbarRing.Round.Slot.not_before_of_reach (m := S.full) hX hpath
          refine ⟨k, w, sk, ?_, hk, hww, hsk, by rw [hskp]; omega⟩
          rcases Nat.lt_trichotomy k i with hki | rfl | hki
          · exact hki
          · rw [hi] at hk
            have hrw : w = r := (Option.some.inj hk).symm
            subst hrw
            obtain ⟨-, p, -, hact, -⟩ := hch.okPoll hi hww
            rw [ha] at hact
            cases hact
          · exact absurd ⟨i, k, r, w, hi, hid, hk, hwid, hki⟩ hnb)
      first | exact hff.2 h | exact hff.1 h

/-- **Fault freedom of an empty barrier.** -/
theorem empty_fault_free (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2} :
    ∀ r ∈ X.objects (S.empty a), r.fault = none := by
  classical
  intro r hr
  set log := X.objects (S.empty a) with hlog
  have hch : CheckedLog log := X.objects_checked hX (S.empty a)
  have hni := H.empty_noInval a
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hil : i ≤ log.length := (List.getElem?_eq_some_iff.mp hi).1.le
  cases ha : r.action with
  | inval => exact (hni r hr ha).elim
  | increment =>
    exfalso
    cases H.empty_src a r hr with
    | init ha' | poll _ _ ha' | notify _ _ _ _ ha' _ => rw [ha] at ha'; cases ha'
  | init n =>
    exact init_clean (H.empty_init a) hr ha
  | pollParity p ok => exact empty_poll_clean hX H r hr ⟨p, ok, ha⟩
  | completeTx n =>
    exfalso
    cases H.empty_src a r hr with
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | notify _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive n tx =>
    obtain ⟨rfl, rfl, b, j, pc, sp, hid, he, hm, htg, hcb⟩ := notify_consumer H hr ha
    obtain ⟨-, st, hst, -⟩ := state_of_init hX (H.empty_init a) (H.empty_noInval a) hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    have htx := empty_tx_zero hX H hil hst'
    have hok := hch.at hi
    rw [hst'] at hok
    rcases arrive_fault_cases hok ha (by unfold validCount limit; omega)
      (by unfold validTxOperand; omega) (by rw [htx]; unfold validTx limit; omega) with h | h | h
    · exact h
    all_goals
      exfalso
      have hf : r.fault ≠ none := by rw [h]; simp
      set t := ((X.tr (S.cons b)).take j).countP (commitsTo (S.empty 0))
        with ht'
      have hp : commitsTo (S.empty 0) ⟨pc, .tc (.commit sp)⟩ = true := by
        simp [commitsTo, hm]
      have hit : note X S b a t = r.id := by
        rw [hid]
        simp only [note, cm, ht']
        rw [nthEv_eq he hp]
      -- the notification is not counted, so no counted notification has a later use
      have hnot : (b, t) ∉ SE X S a := by
        intro hy
        obtain ⟨-, r', hr', hid', hf', -⟩ := Finset.mem_filter.mp hy
        rw [hX.record_eq hr' hr (hid'.trans hit)] at hf'
        exact hf hf'
      have hle : ∀ y ∈ SE X S a, y.2 ≤ t := by
        intro y hy
        by_contra hgt
        have hg := guardM H hy (j := t + 1) (by omega)
        have hpw := MbarRing.Round.Slot.present_of_guard hg
        obtain ⟨hx, -⟩ := consumer_observes hX H (MbarRing.Poll.nth_present.mp hpw)
          (copyKind S.n a 0 H.n_pos)
        have hu := SF_use_lt H hx
        rw [kOwner_copyKind] at hu
        exact hnot (producer_observes hX H (n := t) (by simpa using hu) b).1
      have hunits : unitsBefore log i < nc * (t + 1) := by
        have h1 :=
          MbarRing.Round.units_le_of_uses hch (fun y : Fin nc × Nat => note X S y.1 a y.2)
          (SE X S a) (i := i)
          (fun k r c' tx hr hf ha => (empty_count H k r c' tx hr hf ha).1)
          (fun k _ r' c' tx hr' hf' ha' => (empty_count H k r' c' tx hr' hf' ha').2)
        have h2 := MbarRing.Round.card_lt_of_uses (SE X S a) (Q := t + 1)
          (fun y hy => Nat.lt_succ_of_le (hle y hy)) (z := (b, t)) (by simp) hnot
        simp only [Fintype.card_fin] at h2
        omega
      have hguard : ∀ j' ≤ t, Resumes K X ((ring hX H).wF b j')
          (S.cons b, j) := fun j' hj' =>
        MbarRing.Poll.guard H.spins (len_of_get he) (by omega)
      have hnp := object_record_present hX.tma hr
      rw [hid] at hnp
      have hff := hch.arrive_fault_free hni (s := t) hi ha
        (fun st' hs => by
          rw [expected_of_init hX (H.empty_init a) (H.empty_noInval a) hs]
          exact hunits)
        (fun q hq1 hqt => by
          obtain ⟨hpw, hpath⟩ := (ring hX H).reach_consumer_op hX.depAcyclic a
            hguard hq1 hqt
          have hpath' : Relation.TransGen (DepStep L K X)
              (.thread ((ring hX H).wE a q), true) (r.id, false) := by
            rw [hid]
            exact hpath.tail (.inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hnp, trivial⟩))
          obtain ⟨k, w, sk, hk, hwid, hww, hsk, hskp, -⟩ :=
            E_found hX H hq1 (MbarRing.Poll.nth_present.mp hpw)
          have hnb := MbarRing.Round.Slot.not_before_of_reach (m := S.empty a) hX
            hpath'
          refine ⟨k, w, sk, ?_, hk, hww, hsk, hskp⟩
          rcases Nat.lt_trichotomy k i with hki | rfl | hki
          · exact hki
          · rw [hi] at hk
            have hrw : w = r := (Option.some.inj hk).symm
            subst hrw
            obtain ⟨-, p, -, hact, -⟩ := hch.okPoll hi hww
            rw [ha] at hact
            cases hact
          · exact absurd ⟨i, k, r, w, hi, rfl, hk, hwid, hki⟩ hnb)
      first | exact hff.2 h | exact hff.1 h

/-- **Every record of the input ring's objects is fault-free.** -/
theorem fault_free (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {m : Loc}
    (hm : m = S.full ∨ ∃ a, m = S.empty a) {r : Record Ref} (hr : r ∈ X.objects m) :
    r.fault = none := by
  rcases hm with rfl | ⟨a, rfl⟩
  · exact full_fault_free hX H r hr
  · exact empty_fault_free hX H r hr

end
end PTX.PairTmaRing
