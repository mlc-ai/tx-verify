-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.RingFacts
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # The records of a single-CTA ring slot are fault-free

A proof tool (generalized from the Inkling KV ring). Under `Hyp`, every record of the slot's
barriers is fault-free (`fault_free`). The initialization is the barrier's first record and only
one; polls find its state. A completion of `full` keeps its transaction counter within range
(`full_tx_bounds`). An arrival, of `full` by the arrival thread or the preloading arrival, or of
`empty` by the consumer's commit, carries valid operands and keeps the counter in range; it
neither underflows nor arrives in an unobserved phase: were it faulting, its item would not be
counted, so no counted item of its kind has a later use, which bounds the arrival units before
it; and the pollers' polls for the earlier uses precede it in the barrier's history, where they
found the phases up to its use (`F_found`, `E_found`). -/

namespace PTX.SingleTmaRing
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section


variable {X : Execution} {S : Slot} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {sc : MbarScope}

/-- An arrival on the full barrier is the item of kind `0` of some use `u`, guarded by the
loader's polls of `empty` for the uses `1, …, u` (none for the prologue's, whose use is 0). -/
theorem arrival_use (H : Hyp L K A X S sc) {r : Record Ref} (hr : r ∈ X.objects S.full)
    {n tx : Nat} (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = S.tx ∧ ∃ u, itF X S ⟨0, by omega⟩ u = r.id ∧
      ∀ m, 1 ≤ m → m ≤ u → Resumes K X (wE X S 0 m) (opF X S ⟨0, by omega⟩ u) := by
  classical
  obtain ⟨rfl, rfl, hs⟩ := arrival_source H hr ha
  refine ⟨rfl, rfl, ?_⟩
  have hδ := H.δ_le
  rcases hs with ⟨j, pc, rel, sc, hid, he, hab⟩ | ⟨hδ1, hid, pc, rel, sc, he⟩
  · have hp : arrivesOn S.full ⟨pc, .arrive S.full S.tx 1 rel sc⟩ = true := by
      simp [arrivesOn, sourceArrive]
    set a := arrivals S.full ((X.tr S.ap).take j) with ha'
    have hnz : ¬ (S.δ = 1 ∧ a + S.δ = 0) := fun h => by omega
    have hop : opF X S ⟨0, by omega⟩ (a + S.δ) = (S.ap, j) := by
      rw [opF_ld hnz, kOwner_zero, prod_zero, kPred_zero, kIdx_zero, Nat.add_sub_cancel]
      simp only [ha']
      unfold arrivals
      rw [nthEv_eq he hp]
    refine ⟨a + S.δ, ?_, ?_⟩
    · simp only [itF, ↓reduceIte]
      rw [hop, hid]
    · intro m h1 hm
      rw [hop]
      simp only [wE, prod_zero]
      exact MbarRing.Poll.guard H.spins (len_of_get he) (by omega)
  · refine ⟨0, ?_, fun m h1 hm => by omega⟩
    simp only [itF, ↓reduceIte]
    rw [opF_pre_zero hδ1, hid]

/-- **Fault freedom of the full barrier.** -/
theorem full_fault_free (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) :
    ∀ r ∈ X.objects S.full, r.fault = none := by
  classical
  intro r hr
  set log := X.objects S.full with hlog
  have hch : CheckedLog log := X.objects_checked hX S.full
  have hni := H.full_noInval
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hil : i ≤ log.length := (List.getElem?_eq_some_iff.mp hi).1.le
  cases ha : r.action with
  | inval => exact (hni r hr ha).elim
  | increment =>
    exfalso
    cases H.full_src r hr with
    | init ha' | poll _ _ ha' | arrive _ _ ha' _ | preArrive _ _ _ ha' | copy _ _ _ ha' _
    | preCopy _ _ _ _ ha' => rw [ha] at ha'; cases ha'
  | init n =>
    exact PairTmaRing.init_clean H.full_init hr ha
  | pollParity p ok => exact full_poll_clean hX H r hr ⟨p, ok, ha⟩
  | completeTx n =>
    obtain ⟨rfl, -⟩ := completion_source H hr ha
    obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX H.full_init H.full_noInval hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    obtain ⟨hlo, hhi⟩ := full_tx_bounds hX H hP hil hst'
    have hok := hch.at hi
    rw [hst'] at hok
    have h1 := hP.2.2
    have h2 := hP.bytes_le
    exact PairTmaRing.complete_fault_free hok ha (by unfold validTxOperand; exact hP.bytes_lt)
      (by unfold validTx; omega)
  | arrive n tx =>
    obtain ⟨rfl, rfl, u, hit, hguard⟩ := arrival_use (K := K) H hr ha
    obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX H.full_init H.full_noInval hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    obtain ⟨hlo, hhi⟩ := full_tx_bounds hX H hP hil hst'
    have hok := hch.at hi
    rw [hst'] at hok
    have h1 := hP.2.2
    rcases PairTmaRing.arrive_fault_cases hok ha (by unfold validCount limit; omega)
      (by unfold validTxOperand; exact hP.tx_lt)
      (by unfold validTx; omega) with h | h | h
    · exact h
    all_goals
      exfalso
      have hf : r.fault ≠ none := by rw [h]; simp
      -- the arrival is not counted, so no counted arrival has a later use
      have hnot : ((⟨0, by omega⟩ : Kind S), u) ∉ SF X S := by
        intro hx
        obtain ⟨-, r', hr', hid', hf', -⟩ := Finset.mem_filter.mp hx
        rw [hX.record_eq hr' hr (hid'.trans hit)] at hf'
        exact hf hf'
      have hle : ∀ x ∈ SF X S, x.2 ≤ u := by
        intro x hx
        by_contra hgt
        obtain ⟨hp', -⟩ := SF_reach hX H hP hx 0 (j := u) (by omega)
        exact hnot (consumer_observes hX H hP (b := 0) (MbarRing.Poll.nth_present.mp hp')
          ⟨0, by omega⟩).1
      have hunits : unitsBefore log i ≤ u := by
        have h := MbarRing.Round.units_le_of_uses hch
          (fun y : Unit × Nat => itF X S ⟨0, by omega⟩ y.2)
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
      have hff := hch.arrive_fault_free hni (s := u) hi ha
        (fun st' hs => by
          rw [PairTmaRing.expected_of_init hX H.full_init H.full_noInval hs]
          omega)
        (fun q hq1 hqu => by
          obtain ⟨hpw, hpath⟩ := (ring hX H hP).reach_op hX.depAcyclic hguard
            (b := 0) (j := q - 1) (by omega)
          obtain ⟨k, w, sk, hk, hwid, hww, hsk, hskp, -⟩ :=
            F_found hX H hP (b := 0) (MbarRing.Poll.nth_present.mp hpw)
          have hnb := MbarRing.Round.Slot.not_before_of_reach (m := S.full) hX hpath
          have hpath' : Relation.TransGen (DepStep L K X)
              (.thread ((ring hX H hP).wF 0 (q - 1)), true) (r.id, false) := by
            rw [← hit]
            exact hpath
          refine ⟨k, w, sk, ?_, hk, hww, hsk, by rw [hskp]; omega⟩
          rcases Nat.lt_trichotomy k i with hki | rfl | hki
          · exact hki
          · rw [hi] at hk
            have hrw : w = r := (Option.some.inj hk).symm
            subst hrw
            obtain ⟨-, p, -, hact, -⟩ := hch.okPoll hi hww
            rw [ha] at hact
            cases hact
          · exact absurd ⟨i, k, r, w, hi, hit.symm, hk, hwid, hki⟩ hnb)
      first | exact hff.2 h | exact hff.1 h

/-- **Fault freedom of the empty barrier.** -/
theorem empty_fault_free (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) :
    ∀ r ∈ X.objects S.empty, r.fault = none := by
  classical
  intro r hr
  set log := X.objects S.empty with hlog
  have hch : CheckedLog log := X.objects_checked hX S.empty
  have hni := H.empty_noInval
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hil : i ≤ log.length := (List.getElem?_eq_some_iff.mp hi).1.le
  cases ha : r.action with
  | inval => exact (hni r hr ha).elim
  | increment =>
    exfalso
    cases H.empty_src r hr with
    | init ha' | poll _ _ ha' | notify _ _ _ _ ha' _ => rw [ha] at ha'; cases ha'
  | init n =>
    exact PairTmaRing.init_clean H.empty_init hr ha
  | pollParity p ok => exact empty_poll_clean hX H r hr ⟨p, ok, ha⟩
  | completeTx n =>
    exfalso
    cases H.empty_src r hr with
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | notify _ _ _ _ ha' _ => rw [ha] at ha'; cases ha'
  | arrive n tx =>
    obtain ⟨rfl, rfl, j, pc, sp, hid, he, hm, htg, hcb⟩ := notify_source H hr ha
    obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX H.empty_init H.empty_noInval hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    have htx := empty_tx_zero hX H hil hst'
    have hok := hch.at hi
    rw [hst'] at hok
    rcases PairTmaRing.arrive_fault_cases hok ha (by unfold validCount limit; omega)
      (by unfold validTxOperand; omega) (by rw [htx]; unfold validTx limit; omega) with h | h | h
    · exact h
    all_goals
      exfalso
      have hf : r.fault ≠ none := by rw [h]; simp
      set t := ((X.tr S.cm).take j).countP (commitsTo S.empty) with ht'
      have hp : commitsTo S.empty ⟨pc, .tc (.commit sp)⟩ = true := by
        simp [commitsTo, hm]
      have hit : note X S 0 0 t = r.id := by
        rw [hid]
        simp only [note, cmE, ht']
        rw [nthEv_eq he hp]
      -- the notification is not counted, so no counted notification has a later use
      have hnot : ((0 : Fin 1), t) ∉ SE X S := by
        intro hy
        obtain ⟨-, r', hr', hid', hf', -⟩ := Finset.mem_filter.mp hy
        rw [hX.record_eq hr' hr (hid'.trans hit)] at hf'
        exact hf hf'
      have hle : ∀ y ∈ SE X S, y.2 ≤ t := by
        intro y hy
        by_contra hgt
        have hg := guardM H hy (j := t + 1) (by omega)
        have hpw := MbarRing.Round.Slot.present_of_guard hg
        obtain ⟨hx, -⟩ := consumer_observes hX H hP (b := y.1) (MbarRing.Poll.nth_present.mp hpw)
          (⟨1, by have := hP.1; omega⟩ : Kind S)
        obtain ⟨-, -, hs⟩ := SF_op H hx
        have hδ := H.δ_le
        rcases hs with ⟨-, hu⟩ | ⟨j', hj', hb'⟩
        · omega
        · have hk1 : kOwner (⟨1, by have := hP.1; omega⟩ : Kind S) = 1 := kOwner_ne (by simp)
          rw [hk1, prod_one] at hb'
          have hb'' := hb'.trans (okPolls_take_le _ _ _)
          rw [← prod_one (S := S)] at hb''
          have hl : t + 1 - S.δ < okPolls S.empty (X.tr (S.prod 1)) := by simp only at hb'' ⊢; omega
          exact hnot (producer_observes hX H hP (a := 1) (n := t) hl 0).1
      have hunits : unitsBefore log i < 1 * (t + 1) := by
        have h1 := MbarRing.Round.units_le_of_uses hch
          (fun y : Fin 1 × Nat => note X S y.1 0 y.2)
          (SE X S) (i := i)
          (fun k r c' tx hr hf ha => (empty_count H k r c' tx hr hf ha).1)
          (fun k _ r' c' tx hr' hf' ha' => (empty_count H k r' c' tx hr' hf' ha').2)
        have h2 := MbarRing.Round.card_lt_of_uses (SE X S) (Q := t + 1)
          (fun y hy => Nat.lt_succ_of_le (hle y hy)) (z := (0, t)) (by simp) hnot
        simp only [Fintype.card_fin] at h2
        omega
      have hguard : ∀ j' ≤ t, Resumes K X ((ring hX H hP).wF 0 j') (S.cm, j) := fun j' hj' =>
        MbarRing.Poll.guard H.spins (len_of_get he) (by omega)
      have hnp := object_record_present hX.tma hr
      rw [hid] at hnp
      have hff := hch.arrive_fault_free hni (s := t) hi ha
        (fun st' hs => by
          rw [PairTmaRing.expected_of_init hX H.empty_init H.empty_noInval hs]
          exact hunits)
        (fun q hq1 hqt => by
          obtain ⟨hpw, hpath⟩ := (ring hX H hP).reach_consumer_op hX.depAcyclic 0
            (b := 0) (op := (S.cm, j)) hguard hq1 hqt
          have hpath' : Relation.TransGen (DepStep L K X)
              (.thread ((ring hX H hP).wE 0 q), true) (r.id, false) := by
            rw [hid]
            exact hpath.tail (.inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hnp, trivial⟩))
          have hpw' := MbarRing.Poll.nth_present.mp hpw
          obtain ⟨k, w, sk, hk, hwid, hww, hsk, hskp, -⟩ :=
            E_found hX H hP (a := 0) hq1 hpw'
          have hnb := MbarRing.Round.Slot.not_before_of_reach (m := S.empty) hX hpath'
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

/-- **Every record of the ring slot's barriers is fault-free.** -/
theorem fault_free (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) {m : Loc}
    (hm : m = S.full ∨ m = S.empty) {r : Record Ref} (hr : r ∈ X.objects m) :
    r.fault = none := by
  rcases hm with rfl | rfl
  · exact full_fault_free hX H hP r hr
  · exact empty_fault_free hX H hP r hr

end
end PTX.SingleTmaRing
