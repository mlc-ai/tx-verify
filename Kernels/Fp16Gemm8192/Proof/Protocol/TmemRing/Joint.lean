-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Ring

@[expose] public section

/-! # The accumulator ring's phases and fault freedom

From the ring of items (`ring`), read through each barrier's own history: consumer `b`'s
successful full poll with `t` earlier ones found phase `t + 1` (`cons_poll_phase`), and the
producer's successful empty poll with `n ≥ 1` earlier ones found phase `n`
(`prod_poll_phase`). An arrival on a buffer's barrier neither underflows nor arrives in a phase
whose predecessor was not observed (`full_arrive_ok`, `empty_arrive_ok`): its use bounds the
counted arrivals before it, and the polls of the uses below it precede it in the dependency
order. So
every record of the ring's barriers is fault-free (`fault_free`, `tmemFacts`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The counted arrivals of consumer `b`'s full barrier are the notifications of `SF`. -/
theorem full_count (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} :
    ∀ (i : Nat) (r : Record Ref) (n tx : Nat), (X.objects ((slot L c j).full k))[i]? = some r →
      r.fault = none → r.action = .arrive n tx →
      n = 1 ∧ ∃ x ∈ (fullItems L X c j k).filter (fun x => x.1 ∈ (Finset.univ : Finset (Fin 1))),
        r.id = notifyRef L X c j k x.2 := by
  classical
  intro i r n tx hi hf ha
  obtain ⟨rfl, rfl⟩ := acc_unit (cta := 2 * c + k.val) (f := true) hX ht i r n tx hi hf ha
  obtain ⟨x, hx, hid⟩ := fullItems_of_record hpre hX ht (List.mem_of_getElem? hi) hf ha
  exact ⟨rfl, x, Finset.mem_filter.mpr ⟨hx, Finset.mem_univ _⟩, hid⟩

/-- The counted arrivals of the empty barrier are the arrivals of `SE`. -/
theorem empty_count (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} :
    ∀ (i : Nat) (r : Record Ref) (n tx : Nat), (X.objects ((slot L c j).empty 0))[i]? = some r →
      r.fault = none → r.action = .arrive n tx →
      n = 1 ∧ ∃ y ∈ emptyItems L X c j, r.id = arriveRef L X c j y.1 y.2 := by
  intro i r n tx hi hf ha
  obtain ⟨rfl, rfl⟩ := acc_unit (cta := 2 * c) (f := false) hX ht i r n tx hi hf ha
  exact ⟨rfl, emptyItems_of_record hpre hX ht (List.mem_of_getElem? hi) hf ha⟩

/-- **A consumer's full poll finds its phase.** Consumer `b`'s successful full poll with `t`
earlier ones has a fault-free record that found phase `t + 1`. -/
theorem cons_poll_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {t : Nat}
    (h : t < okPolls ((slot L c j).full ((slot L c j).owner b)) (X.tr (consumerOf L c j b))) :
    ∃ k w, (X.objects ((slot L c j).full ((slot L c j).owner b)))[k]? = some w ∧
      w.id = .thread (consPoll L X c j b t) ∧ w.reply.waited = some true ∧ w.fault = none ∧
      ∃ st, stateBefore (X.objects ((slot L c j).full ((slot L c j).owner b))) k = some st ∧
        st.phase = t + 1 := by
  obtain ⟨k, w, hk, hwid, hww, hwf, hsel⟩ := consPoll_record hpre hX ht h
  obtain ⟨st, hst, hph⟩ := (ring hpre hX ht c j).full_poll_phase hX (b := b) Finset.univ
    (by simp) (objects_noInval hX ht _) (objectThreadSelected (consumerOf L c j b)) (δ := 0)
        (by omega)
    (cons_alt hpre hX ht c j b) (full_count hpre hX ht)
    (fun k st hs => by
      rw [expected_eq (cta := 2 * c + b.val / 128) (f := true) hpre hX ht k st hs]
      rfl)
    hk hwid hww (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hsel
  exact ⟨k, w, hk, hwid, hww, hwf, st, hst, hph⟩

/-- **The producer's empty poll finds its phase.** The producer's successful empty poll with
`n ≥ 1` earlier ones has a fault-free record that found phase `n`. -/
theorem prod_poll_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {n : Nat} (hn : 1 ≤ n)
    (h : n < okPolls ((slot L c j).empty 0) (X.tr (producer L X c j))) :
    ∃ k w, (X.objects ((slot L c j).empty 0))[k]? = some w ∧
      w.id = .thread (prodPoll L X c j n) ∧ w.reply.waited = some true ∧ w.fault = none ∧
      ∃ st, stateBefore (X.objects ((slot L c j).empty 0)) k = some st ∧ st.phase = n := by
  obtain ⟨k, w, hk, hwid, hww, hwf, hsel⟩ := prodPoll_record hpre hX ht h
  obtain ⟨st, hst, hph⟩ := (ring hpre hX ht c j).empty_poll_phase hX (by decide)
      (objects_noInval hX ht _) (a := 0)
    (objectThreadSelected (producer L X c j)) (δ := 1) le_rfl (prod_alt hpre hX ht c j)
    (empty_count hpre hX ht) (expected_eq (cta := 2 * c) (f := false) hpre hX ht) hn hk hwid hww
    (objectThreadSelected_iff.mpr ⟨_, hwid⟩) (by rw [hsel]; omega)
  exact ⟨k, w, hk, hwid, hww, hwf, st, hst, hph⟩

/-- Consumer `128 k` polls full barrier `k`. -/
theorem owner_first (c : Nat) (j k : Fin 2) :
    (slot L c j).owner ⟨128 * k.val, by omega⟩ = k :=
  Fin.ext (by simp only [slot]; omega)

/-- A poll record that precedes an update in the dependency order is before it in the update's
history. -/
theorem poll_before {mem0 : Mem0} (hX : Consistent L kernel Prod mem0 X) {m : Loc} {i k : Nat}
    {r w : Record Ref} (hi : (X.objects m)[i]? = some r) (ha : r.action = .arrive 1 0)
    (hk : (X.objects m)[k]? = some w) (hww : w.reply.waited = some true)
    (hpath : Relation.TransGen (DepStep L kernel X) (w.id, true) (r.id, false)) : k < i := by
  rcases Nat.lt_trichotomy k i with h | rfl | h
  · exact h
  · rw [hi] at hk
    cases hk
    obtain ⟨-, p, -, hact, -⟩ := (X.objects_checked hX m).okPoll hi hww
    rw [ha] at hact
    cases hact
  · exact absurd ⟨i, k, r, w, hi, rfl, hk, rfl, h⟩
      (MbarRing.Round.Slot.not_before_of_reach hX hpath)

/-- **Fault freedom of a full barrier.** A notification on buffer `j`'s full barrier `k`
neither underflows nor arrives in a phase whose predecessor was not observed. -/
theorem full_arrive_ok (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {i : Nat} {r : Record Ref}
    (hi : (X.objects ((slot L c j).full k))[i]? = some r) (ha : r.action = .arrive 1 0) :
    r.fault ≠ some .arrivalUnderflow ∧ r.fault ≠ some .precedingPhaseNotObserved := by
  classical
  by_cases hf : r.fault = none
  · rw [hf]; simp
  have hacyc := hX.depAcyclic
  have hch := X.objects_checked hX ((slot L c j).full k)
  have hni := objects_noInval hX ht ((slot L c j).full k)
  have hr := List.mem_of_getElem? hi
  obtain ⟨jc, pc, sp, hid, he, hmb, htg, hnot⟩ := notify_record hpre hX ht hr ha
  have hp : commitsTo ((slot L c j).full 0) ⟨pc, .tc (.commit sp)⟩ = true := by
    simp [commitsTo, hmb]
  set s := ((X.tr (producer L X c j)).take jc).countP (commitsTo ((slot L c j).full 0)) with hsdef
  have hs : commitAt L X c j s = jc := nthEv_eq he hp
  have hid' : r.id = notifyRef L X c j k s := by rw [hid, notifyRef, hs]
  have hns : ((0 : Fin 1), s) ∉ fullItems L X c j k := fun h => by
    obtain ⟨r', hr', hid'', hf'⟩ := fullItems_mem h
    exact hf (hX.record_eq hr hr' (hid'.trans hid''.symm) ▸ hf')
  set b : Fin 256 := ⟨128 * k.val, by omega⟩
  have hown := owner_first (L := L) c j k
  -- every counted notification is of a use at most `s`
  have hle : ∀ x ∈ fullItems L X c j k, x.2 ≤ s := by
    intro x hx
    by_contra hgt
    have hg := (ring hpre hX ht c j).guardP k x hx (s + 1) (by omega) (by omega)
    obtain ⟨hy, -⟩ := (ring hpre hX ht c j).observes_empty hacyc
      (MbarRing.Round.Slot.present_of_guard hg) b
    have hgM := (ring hpre hX ht c j).guardM 0 (b, s) hy s le_rfl
    obtain ⟨hx', -⟩ := (ring hpre hX ht c j).observes_full hacyc
      (MbarRing.Round.Slot.present_of_guard hgM) 0
    change ((0 : Fin 1), s) ∈ fullItems L X c j ((slot L c j).owner b) at hx'
    rw [hown] at hx'
    exact hns hx'
  have hguard : ∀ n, 1 ≤ n → n ≤ s →
      Resumes kernel X ((ring hpre hX ht c j).wE 0 n) (producer L X c j, jc) :=
    fun n _ hn => commit_guard hpre hX ht he htg (by omega)
  refine hch.arrive_fault_free hni (s := s) hi ha (fun st hst => ?_) (fun q hq1 hqs => ?_)
  · rw [expected_eq (cta := 2 * c + k.val) (f := true) hpre hX ht i st hst]
    have hu := MbarRing.Round.units_le_of_uses hch (fun x : Fin 1 × Nat => notifyRef L X c j k x.2)
      (fullItems L X c j k) (i := i)
      (fun k' r' n tx hr' hf' ha' => (full_count hpre hX ht k' r' n tx hr' hf' ha').1)
      (fun k' _ r' n tx hr' hf' ha' => by
        obtain ⟨-, x, hx, hid⟩ := full_count hpre hX ht k' r' n tx hr' hf' ha'
        exact ⟨x, (Finset.mem_filter.mp hx).1, hid⟩)
    have hc := MbarRing.Round.card_lt_of_uses (fullItems L X c j k) (Q := s + 1)
      (fun x hx => Nat.lt_succ_of_le (hle x hx)) (z := (0, s)) (by simp) hns
    simp only [Fintype.card_fin] at hc
    change unitsBefore _ i < 1 * (s + 1)
    omega
  · obtain ⟨hpres, hpath⟩ := (ring hpre hX ht c j).reach_op hacyc hguard b (j := q - 1) (by omega)
    have hpath' : Relation.TransGen (DepStep L kernel X)
        (.thread (consPoll L X c j b (q - 1)), true) (r.id, false) :=
      hpath.tail (by
        rw [hid]; exact DepStep.issue ⟨_, he⟩ hnot (by simp) (by simp) (by simp) (by simp))
    obtain ⟨k', w, hk', hwid, hww, -, st, hst, hph⟩ := cons_poll_phase hpre hX ht
      ((MbarRing.Poll.nth_present (X := X)).mp hpres)
    rw [hown] at hk' hst
    rw [← hwid] at hpath'
    exact ⟨k', w, st, poll_before hX hi ha hk' hww hpath', hk', hww, hst, by omega⟩

/-- **Fault freedom of the empty barrier.** A consumer's arrival on buffer `j`'s empty barrier
neither underflows nor arrives in a phase whose predecessor was not observed. -/
theorem empty_arrive_ok (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {i : Nat} {r : Record Ref}
    (hi : (X.objects ((slot L c j).empty 0))[i]? = some r) (ha : r.action = .arrive 1 0) :
    r.fault ≠ some .arrivalUnderflow ∧ r.fault ≠ some .precedingPhaseNotObserved := by
  classical
  by_cases hf : r.fault = none
  · rw [hf]; simp
  have hacyc := hX.depAcyclic
  have hch := X.objects_checked hX ((slot L c j).empty 0)
  have hni := objects_noInval hX ht ((slot L c j).empty 0)
  have hr := List.mem_of_getElem? hi
  obtain ⟨b, ka, pc, rel, sc, hid, he⟩ := empty_arrival hpre hX ht hr ha
  have hp : arrivesOn ((slot L c j).empty 0) ⟨pc, .arrive ((slot L c j).empty 0) 0 1 rel sc⟩ =
      true := by simp [sourceArrive]
  set t := ((X.tr (consumerOf L c j b)).take ka).countP (arrivesOn ((slot L c j).empty 0))
    with htdef
  have hs : arriveAt L X c j b t = ka := nthEv_eq he hp
  have hid' : r.id = arriveRef L X c j b t := by rw [hid, arriveRef, hs]
  have hnt : (b, t) ∉ emptyItems L X c j := fun h => by
    obtain ⟨r', hr', hid'', hf'⟩ := emptyItems_mem h
    exact hf (hX.record_eq hr hr' (hid'.trans hid''.symm) ▸ hf')
  -- every counted arrival is of a use at most `t`
  have hle : ∀ y ∈ emptyItems L X c j, y.2 ≤ t := by
    intro y hy
    by_contra hgt
    have hgM := (ring hpre hX ht c j).guardM 0 y hy (t + 1) (by omega)
    obtain ⟨hx, -⟩ := (ring hpre hX ht c j).observes_full hacyc
      (MbarRing.Round.Slot.present_of_guard hgM) 0
    have hgP := (ring hpre hX ht c j).guardP _ (0, t + 1) hx (t + 1) (by omega) le_rfl
    exact hnt ((ring hpre hX ht c j).observes_empty hacyc
      (MbarRing.Round.Slot.present_of_guard hgP) b).1
  have hguard : ∀ j' ≤ t,
      Resumes kernel X ((ring hpre hX ht c j).wF b j') (consumerOf L c j b, ka) :=
    fun j' hj' => arrive_guard hpre hX ht he hj'
  refine hch.arrive_fault_free hni (s := t) hi ha (fun st hst => ?_) (fun q hq1 hqs => ?_)
  · rw [expected_eq (cta := 2 * c) (f := false) hpre hX ht i st hst]
    have hu := MbarRing.Round.units_le_of_uses hch
      (fun y : Fin 256 × Nat => arriveRef L X c j y.1 y.2) (emptyItems L X c j) (i := i)
      (fun k' r' n tx hr' hf' ha' => (empty_count hpre hX ht k' r' n tx hr' hf' ha').1)
      (fun k' _ r' n tx hr' hf' ha' => (empty_count hpre hX ht k' r' n tx hr' hf' ha').2)
    have hc := MbarRing.Round.card_lt_of_uses (emptyItems L X c j) (Q := t + 1)
      (fun y hy => Nat.lt_succ_of_le (hle y hy)) (z := (b, t)) (by simp) hnt
    simp only [Fintype.card_fin] at hc
    change unitsBefore _ i < 256 * (t + 1)
    omega
  · obtain ⟨hpres, hpath⟩ := (ring hpre hX ht c j).reach_consumer_op hacyc 0 hguard hq1 hqs
    obtain ⟨k', w, hk', hwid, hww, -, st, hst, hph⟩ := prod_poll_phase hpre hX ht hq1
      ((MbarRing.Poll.nth_present (X := X)).mp hpres)
    have hpath' : Relation.TransGen (DepStep L kernel X) (w.id, true) (r.id, false) := by
      rw [hwid, hid]
      exact hpath
    exact ⟨k', w, st, poll_before hX hi ha hk' hww hpath', hk', hww, hst, hph⟩

/-- **Fault freedom.** Every record of a buffer's barriers is fault-free. -/
theorem fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) (j : Fin 2) {m : Loc} (hm : m ∈ (slot L c j).objects) :
    ∀ r ∈ X.objects m, r.fault = none := by
  intro r hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  rcases (slot L c j).objects_cases hm with ⟨k, rfl⟩ | ⟨a, rfl⟩
  · exact acc_fault_free (cta := 2 * c + k.val) (f := true) hpre hX ht hi
      (full_arrive_ok hpre hX ht hi)
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    exact acc_fault_free (cta := 2 * c) (f := false) hpre hX ht hi
      (empty_arrive_ok hpre hX ht hi)

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX AsyncCopy MBarrier

/-- The accumulator ring's facts hold in every execution whose threads have the thread facts. -/
theorem tmemFacts {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) : TmemFacts L X :=
  ⟨fun {i} _ hm => TmemRing.fault_free hpre hX ht i.1 i.2 hm⟩

end PTX.Kernels.Fp16Gemm8192.Proof
