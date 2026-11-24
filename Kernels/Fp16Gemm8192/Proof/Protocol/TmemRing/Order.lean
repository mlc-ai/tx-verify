-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Joint
public import Lemmas.Order.OrderNotAccess

@[expose] public section

/-! # The accumulator ring's records, by phase

The records of a buffer's barriers, located by their phase:

* a consumer's successful poll of its full barrier with `n` earlier successful polls observes the
  barrier's phase `n`, with at least `n + 1` commit notifications before it (`cons_poll`); a
  notification is of a commit of the buffer's producer (`notify_commit`) and lies in the phase
  numbered by the notifications before it (`notify_phase`);
* the producer's successful poll of the empty barrier with `q + 1` earlier successful polls
  observes the barrier's phase `q`, with at least `q + 1` arrivals of each consumer before it
  (`prod_poll`); a consumer's arrival lies in the phase numbered by its earlier arrivals
  (`arrive_phase`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The arrival units of records of an accumulator barrier are its fault-free arrivals. -/
theorem units_eq_isArrival (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {j : Fin 2} {f : Bool} {cta : Nat} :
    ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩)) →
      arrivalUnits xs = xs.countP isArrival := by
  intro xs hxs
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    rw [arrivalUnits, ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq)), List.countP_cons]
    rcases acc_record_cases hX ht (hxs r List.mem_cons_self) with ⟨n, h⟩ | ⟨p, ok, h⟩ | h <;>
      cases hf : r.fault <;> simp [isArrival, h, hf]
    all_goals omega

/-- The successful poll with `n` earlier ones is the one at `jw`. -/
theorem nth_of_get {g jw pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, jw) = some ⟨pc, .wait m p true acq sc⟩) :
    MbarRing.Poll.nth X m g (okPolls m ((X.tr g).take jw)) = jw ∧
      okPolls m ((X.tr g).take jw) < okPolls m (X.tr g) := by
  refine ⟨MbarRing.Poll.nth_eq he, ?_⟩
  have h1 := MbarRing.Poll.okPoll_get he
  have h2 := MbarRing.Poll.okPolls_mono m (X.tr g) (show jw + 1 ≤ (X.tr g).length from
    len_of_get he)
  rw [List.take_length] at h2
  omega

/-- **A consumer's full poll.** A successful poll of consumer `b`'s full barrier with `n` earlier
successful polls has a fault-free record that observes the barrier's phase `n`, with at least
`n + 1` notifications before it. -/
theorem cons_poll (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {jw pc p : Nat} {acq : Bool}
    {sc : MbarScope}
    (hew : X.get (consumerOf L c j b, jw) =
      some ⟨pc, .wait ((slot L c j).full ((slot L c j).owner b)) p true acq sc⟩) :
    ∃ jr r, (X.objects ((slot L c j).full ((slot L c j).owner b)))[jr]? = some r ∧
      r.id = .thread (consumerOf L c j b, jw) ∧ r.fault = none ∧ r.reply.waited = some true ∧
      observedAt (X.objects ((slot L c j).full ((slot L c j).owner b))) jr =
        some (okPolls ((slot L c j).full ((slot L c j).owner b))
          ((X.tr (consumerOf L c j b)).take jw)) ∧
      okPolls ((slot L c j).full ((slot L c j).owner b))
          ((X.tr (consumerOf L c j b)).take jw) + 1 ≤
        ((X.objects ((slot L c j).full ((slot L c j).owner b))).take jr).countP isArrival := by
  obtain ⟨hnth, hlt⟩ := nth_of_get hew
  obtain ⟨k, w, hk, hwid, hww, hwf, st, hst, hph⟩ := cons_poll_phase hpre hX ht hlt
  have hch := X.objects_checked hX ((slot L c j).full ((slot L c j).owner b))
  have hni := objects_noInval hX ht ((slot L c j).full ((slot L c j).owner b))
  have hwid' : w.id = .thread (consumerOf L c j b, jw) := by rw [hwid, consPoll, hnth]
  obtain ⟨st', p', hst', -, -, hcomp⟩ := hch.okPoll hk hww
  rw [hst] at hst'
  cases hst'
  refine ⟨k, w, hk, hwid', hwf, hww, ?_, ?_⟩
  · simp only [observedAt, hk, Option.bind_some, hcomp, hph]
    simp
  · obtain ⟨hp, hu⟩ := (hch.accounted hni (List.getElem?_eq_some_iff.mp hk).1.le).2 st hst
    have hexp := expected_eq (cta := 2 * c + b.val / 128) (f := true) hpre hX ht k st hst
    change st.expected = 1 at hexp
    have hun : unitsBefore (X.objects ((slot L c j).full ((slot L c j).owner b))) k =
        ((X.objects ((slot L c j).full ((slot L c j).owner b))).take k).countP isArrival :=
      units_eq_isArrival (cta := 2 * c + b.val / 128) (f := true) hX ht _
        (fun r hr => List.mem_of_mem_take hr)
    rw [hexp, hph] at hu
    rw [hexp] at hp
    omega

/-- **A notification is of the producer's commit.** A notification on buffer `j`'s full barrier
`k` is of a commit of the buffer's producer to the leader CTA's full barrier, notifying rank `k`. -/
theorem notify_commit (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {x : Record Ref}
    (hx : x ∈ X.objects ((slot L c j).full k)) (hn : isArrival x = true) :
    ∃ jc pc sp, x.id = .async (producer L X c j, jc) (.tcNotify ⟨k.val, by omega⟩) ∧
      X.get (producer L X c j, jc) = some ⟨pc, .tc (.commit sp)⟩ ∧
      sp.mbar = (slot L c j).full 0 ∧
      TcCommit.target sp ⟨k.val, by omega⟩ = some ((slot L c j).full k) := by
  obtain ⟨jc, pc, sp, hid, he, hmb, htg, -⟩ :=
    notify_record hpre hX ht hx ((isArrival_iff x).mp hn).1
  exact ⟨jc, pc, sp, hid, he, hmb, htg⟩

/-- **The phase of a notification.** A notification on a full barrier lies in the phase
numbered by the notifications before it. -/
theorem notify_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {ix : Nat} {x : Record Ref}
    (hx : (X.objects ((slot L c j).full k))[ix]? = some x) (hn : isArrival x = true) :
    phaseAt (X.objects ((slot L c j).full k)) ix =
      some (((X.objects ((slot L c j).full k)).take ix).countP isArrival) := by
  obtain ⟨ha, hf⟩ := (isArrival_iff x).mp hn
  obtain ⟨s, hs⟩ := acc_state (cta := 2 * c + k.val) (f := true) hpre hX ht hx
    (by intro n h; rw [ha] at h; cases h)
  have hexp := expected_eq (cta := 2 * c + k.val) (f := true) hpre hX ht ix s hs
  change s.expected = 1 at hexp
  have hu := (X.objects_checked hX _).full_arrival_phase (objects_noInval hX ht _) hx hs
      (by rw [hexp]; exact ha) hf
  have hun : arrivalUnits ((X.objects ((slot L c j).full k)).take ix) =
      ((X.objects ((slot L c j).full k)).take ix).countP isArrival :=
    units_eq_isArrival (cta := 2 * c + k.val) (f := true) hX ht _
      (fun r hr => List.mem_of_mem_take hr)
  have hs' : stateBefore (X.objects ((slot L c j).full k)) ix = some s := hs
  have hinc := incrementsBefore_eq_zero _
    (incrementsBefore_zero hX ht ((slot L c j).full k)) ix
  have hacc := ((X.objects_checked hX ((slot L c j).full k)).accounted (objects_noInval hX ht _)
    (List.getElem?_eq_some_iff.mp hx).1.le).2 s hs'
  rw [hexp, Nat.one_mul, unitsBefore, hun, hinc] at hu
  rw [hexp, hinc] at hacc
  have hph : s.phase = ((X.objects ((slot L c j).full k)).take ix).countP isArrival := by omega
  simp [phaseAt, hs', hph]

/-- **The producer's empty poll.** A successful poll of buffer `j`'s empty barrier by its
producer, with `q + 1` earlier successful polls, has a fault-free record that observes the
barrier's phase `q`, with at least `q + 1` arrivals of each consumer before it. -/
theorem prod_poll (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {jl pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hwl : X.get (producer L X c j, jl) = some ⟨pc, .wait ((slot L c j).empty 0) p true acq sc⟩)
    {q : Nat} (hq : okPolls ((slot L c j).empty 0) ((X.tr (producer L X c j)).take jl) = q + 1) :
    ∃ jr w, (X.objects ((slot L c j).empty 0))[jr]? = some w ∧
      w.id = .thread (producer L X c j, jl) ∧ w.fault = none ∧ w.reply.waited = some true ∧
      observedAt (X.objects ((slot L c j).empty 0)) jr = some q ∧
      ∀ b, q + 1 ≤ ((X.objects ((slot L c j).empty 0)).take jr).countP
        ((slot L c j).notification 0 b) := by
  have hch := X.objects_checked hX ((slot L c j).empty 0)
  have hni := objects_noInval hX ht ((slot L c j).empty 0)
  obtain ⟨hnth, hlt⟩ := nth_of_get hwl
  rw [hq] at hnth hlt
  obtain ⟨k, w, hk, hwid, hww, hwf, st, hst, hph⟩ := prod_poll_phase hpre hX ht (by omega) hlt
  have hwid' : w.id = .thread (producer L X c j, jl) := by rw [hwid, prodPoll, hnth]
  obtain ⟨st', p', hst', -, -, hcomp⟩ := hch.okPoll hk hww
  rw [hst] at hst'
  cases hst'
  have ho : observedAt (X.objects ((slot L c j).empty 0)) k = some q := by
    simp only [observedAt, hk, Option.bind_some, hcomp, hph]
    simp
  refine ⟨k, w, hk, hwid', hwf, hww, ho, fun b => ?_⟩
  -- consumer `b`'s arrival of use `q` is in the observed phase, so before the poll
  have hw : X.RefPresent (.thread ((ring hpre hX ht c j).wE 0 (q + 1))) :=
    (MbarRing.Poll.nth_present (X := X)).mpr hlt
  obtain ⟨hy, hyp⟩ := ((ring hpre hX ht c j).content_empty hX.depAcyclic hw).2 b
  obtain ⟨r, hr, hid, hf⟩ := emptyItems_mem hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨pca, rel, sca, he, hcnt⟩ := emptyItems_arrive hX ht hy
  obtain ⟨s, hs⟩ := acc_state (cta := 2 * c) (f := false) hpre hX ht hi (by
    intro n h
    have h' := ((hX.tma.2.2.1 _).2.1 r hr).1
    rw [hid, arriveRef] at h'
    simp [objectAction, he, h] at h')
  have hsE : stateBefore (X.objects ((slot L c j).empty 0)) i = some s := hs
  have hphase : phaseAt (X.objects ((slot L c j).empty 0)) i = some q := by
    have h1 := MbarRing.Poll.phaseOf_eq hX hi (q := s.phase) (by simp [phaseAt, hsE])
    have h2 := MbarRing.Poll.observedOf_eq hX hk ho
    change MbarRing.Poll.phaseOf X ((slot L c j).empty 0) (arriveRef L X c j b q) =
      MbarRing.Poll.observedOf X ((slot L c j).empty 0) (.thread (prodPoll L X c j (q + 1))) at hyp
    rw [← hid, ← hwid, h1, h2] at hyp
    simp [phaseAt, hsE, hyp]
  have hik := hch.phase_before_observation hni
      (List.getElem?_eq_some_iff.mp hi).1.le hphase hk hww ho
  have hcount := hX.object_thread_arrival_count_before hi (by rw [hid]; rfl)
  have harr : threadArrival (consumerOf L c j b) r = true := by
    refine threadArrival_iff.mpr ⟨objectThreadSelected_iff.mpr ⟨_, by rw [hid]; rfl⟩, 1, 0, ?_⟩
    have h' := ((hX.tma.2.2.1 _).2.1 r hr).1
    rw [hid, arriveRef] at h'
    simp [objectAction, he] at h'
    exact h'.symm
  have hsucc : ((X.objects ((slot L c j).empty 0)).take (i + 1)).countP
      (threadArrival (consumerOf L c j b)) = q + 1 := by
    rw [List.take_add_one, hi, Option.toList_some, List.countP_append, hcount]
    simp only [List.countP_singleton, harr, ↓reduceIte]
    change arrivals ((slot L c j).empty 0) _ + 1 = q + 1
    rw [hcnt]
  have hmono : ((X.objects ((slot L c j).empty 0)).take (i + 1)).countP
      (threadArrival (consumerOf L c j b)) ≤
      ((X.objects ((slot L c j).empty 0)).take k).countP (threadArrival (consumerOf L c j b)) :=
    (List.take_sublist_take_left (by omega)).countP_le
  change q + 1 ≤ ((X.objects ((slot L c j).empty 0)).take k).countP
    (threadArrival (consumerOf L c j b))
  omega

/-- **An arrival is the consumer's.** An arrival of consumer `b` on buffer `j`'s empty barrier is
a release arrival of the consumer's thread, after as many arrivals there as `b`'s earlier
arrivals in the barrier's log. -/
theorem arrive_record (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {ix : Nat} {x : Record Ref}
    (hx : (X.objects ((slot L c j).empty 0))[ix]? = some x)
    (hn : (slot L c j).notification 0 b x = true) :
    ∃ ja pc tx cnt sc, x.id = .thread (consumerOf L c j b, ja) ∧
      X.get (consumerOf L c j b, ja) =
        some ⟨pc, .arrive ((slot L c j).empty 0) tx cnt true sc⟩ ∧
      sc = .cluster ∧
      arrivals ((slot L c j).empty 0) ((X.tr (consumerOf L c j b)).take ja) =
        ((X.objects ((slot L c j).empty 0)).take ix).countP ((slot L c j).notification 0 b) := by
  have hxm := List.mem_of_getElem? hx
  obtain ⟨hsel, n, m, hact⟩ := threadArrival_iff.mp hn
  obtain ⟨ja, hid⟩ := objectThreadSelected_iff.mp hsel
  obtain ⟨pc, tx, cnt, rel, sc, he⟩ : ∃ pc tx cnt rel sc, X.get (consumerOf L c j b, ja) =
      some ⟨pc, .arrive ((slot L c j).empty 0) tx cnt rel sc⟩ := by
    cases empty_src hX ht hxm with
    | init ha' => rw [hact] at ha'; cases ha'
    | poll _ _ ha' => rw [hact] at ha'; cases ha'
    | arrive hid' he =>
      rw [hid] at hid'
      cases hid'
      exact ⟨_, _, _, _, _, he⟩
    | copy hid' => rw [hid] at hid'; cases hid'
    | clc hid' => rw [hid] at hid'; cases hid'
    | notify hid' => rw [hid] at hid'; cases hid'
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨-, hrel⟩ := ht.sync_flags hg he hσ
  obtain ⟨rfl, rfl⟩ := hrel _ _ _ _ _ rfl
  refine ⟨ja, pc, tx, cnt, .cluster, hid, he, rfl, ?_⟩
  exact (hX.object_thread_arrival_count_before hx hid).symm

/-- **The phase of an arrival.** An arrival of consumer `b` on buffer `j`'s empty barrier lies in
the phase numbered by `b`'s earlier arrivals there. -/
theorem arrive_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {ix : Nat} {x : Record Ref}
    (hx : (X.objects ((slot L c j).empty 0))[ix]? = some x)
    (hn : (slot L c j).notification 0 b x = true) :
    x.fault = none ∧ phaseAt (X.objects ((slot L c j).empty 0)) ix =
      some (((X.objects ((slot L c j).empty 0)).take ix).countP
        ((slot L c j).notification 0 b)) := by
  classical
  set R := ring hpre hX ht c j
  have hacyc := hX.depAcyclic
  have hch := X.objects_checked hX ((slot L c j).empty 0)
  have hni := objects_noInval hX ht ((slot L c j).empty 0)
  have hxm := List.mem_of_getElem? hx
  have hxf := fault_free hpre hX ht c j ((slot L c j).empty_mem 0) x hxm
  refine ⟨hxf, ?_⟩
  obtain ⟨ja, pc, tx, cnt, sc, hid, he, -, hcnt⟩ := arrive_record hX ht hx hn
  set t := ((X.objects ((slot L c j).empty 0)).take ix).countP ((slot L c j).notification 0 b)
  have hp : arrivesOn ((slot L c j).empty 0) ⟨pc, .arrive ((slot L c j).empty 0) tx cnt true sc⟩ =
      true := by simp [sourceArrive]
  have hat : arriveAt L X c j b t = ja := by
    rw [arriveAt, ← hcnt]
    exact nthEv_eq he hp
  have ha : x.action = .arrive 1 0 := by
    obtain ⟨-, n, m, hact⟩ := threadArrival_iff.mp hn
    obtain ⟨rfl, rfl⟩ := acc_unit (cta := 2 * c) (f := false) hX ht ix x n m hx hxf hact
    exact hact
  obtain ⟨y, hy, hyid⟩ := emptyItems_of_record hpre hX ht hxm hxf ha
  have hyb : y = (b, t) := by
    rw [hid, arriveRef] at hyid
    simp only [Ref.thread.injEq, Prod.mk.injEq] at hyid
    have hb := consumerOf_inj (L := L) (by rw [hpre.block]; omega) hyid.1
    obtain ⟨-, -, -, -, hc⟩ := emptyItems_arrive hX ht hy
    rw [← hyid.2, ← hb] at hc
    subst hb
    exact Prod.ext rfl (hc.symm.trans hcnt)
  subst hyb
  obtain ⟨s, hs⟩ := acc_state (cta := 2 * c) (f := false) hpre hX ht hx
    (by intro n h; rw [ha] at h; cases h)
  have hsE : stateBefore (X.objects ((slot L c j).empty 0)) ix = some s := hs
  -- the producer's poll of use `t` precedes the arrival
  have hlo : t ≤ s.phase := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · omega
    have hguard : ∀ j' ≤ t, Resumes kernel X (R.wF b j') (consumerOf L c j b, ja) :=
      fun j' hj' => arrive_guard hpre hX ht he (by rw [hcnt]; exact hj')
    obtain ⟨hpres, hpath⟩ := R.reach_consumer_op hacyc 0 hguard hpos le_rfl
    obtain ⟨k, w, hk, hwid, hww, -, st, hst, hph⟩ := prod_poll_phase hpre hX ht hpos
      ((MbarRing.Poll.nth_present (X := X)).mp hpres)
    have hpath' : Relation.TransGen (DepStep L kernel X) (w.id, true) (x.id, false) := by
      rw [hwid, hid]
      exact hpath
    have hki := poll_before hX hx ha hk hww hpath'
    obtain ⟨s', hs', hle⟩ := hch.phase_mono hni hki.le (List.getElem?_eq_some_iff.mp hx).1.le hst
    rw [hsE] at hs'
    cases hs'
    omega
  -- the counted arrivals before it are of uses at most `t`, without itself
  have hhi : s.phase ≤ t := by
    have hexp := expected_eq (cta := 2 * c) (f := false) hpre hX ht ix s hs
    change s.expected = 256 at hexp
    obtain ⟨hlo', -⟩ := hch.unit_arrival_phase hni hx hs ha hxf
    rw [hexp] at hlo'
    let T := (emptyItems L X c j).filter (fun y => y.2 < t + 1 ∧ y ≠ (b, t))
    have hu := MbarRing.Round.units_le_of_uses hch
      (fun y : Fin 256 × Nat => arriveRef L X c j y.1 y.2) T (i := ix)
      (fun k' r' n tx' hr' hf' ha' => (empty_count hpre hX ht k' r' n tx' hr' hf' ha').1)
      (fun k' hk' r' n tx' hr' hf' ha' => by
        obtain ⟨-, y, hy', hid'⟩ := empty_count hpre hX ht k' r' n tx' hr' hf' ha'
        refine ⟨y, Finset.mem_filter.mpr ⟨hy', ?_, fun hyb => ?_⟩, hid'⟩
        · by_contra hge
          have hgM := R.guardM 0 y hy' (t + 1) (by omega)
          obtain ⟨hx1, -⟩ := R.observes_full hacyc (MbarRing.Round.Slot.present_of_guard hgM) 0
          have hgP := R.guardP _ (0, t + 1) hx1 (t + 1) (by omega) le_rfl
          have hw := MbarRing.Round.Slot.present_of_guard hgP
          obtain ⟨hbt, hbp⟩ := (R.content_empty hacyc hw).2 b
          obtain ⟨kw, w, hkw, hwid, hww, -, hsel⟩ := prodPoll_record hpre hX ht
            ((MbarRing.Poll.nth_present (X := X)).mp hw)
          obtain ⟨st, -, -, ho⟩ := MbarRing.Poll.observed_some hch hni (δ := 1) le_rfl
            (prod_alt hpre hX ht c j) hkw (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
            (by rw [hsel]; omega)
          have hphase : phaseAt (X.objects ((slot L c j).empty 0)) ix = some (st.phase - 1) := by
            have h1 := MbarRing.Poll.phaseOf_eq hX hx (q := s.phase) (by simp [phaseAt, hsE])
            have h2 := MbarRing.Poll.observedOf_eq hX hkw ho
            change MbarRing.Poll.phaseOf X ((slot L c j).empty 0) (arriveRef L X c j b t) =
              MbarRing.Poll.observedOf X ((slot L c j).empty 0)
                (.thread (prodPoll L X c j (t + 1))) at hbp
            rw [← hyid, ← hwid, h1, h2] at hbp
            simp [phaseAt, hsE, hbp]
          have h1 := hch.phase_before_observation hni (List.getElem?_eq_some_iff.mp hx).1.le hphase
            hkw hww ho
          have h2 : kw < k' := by
            rcases Nat.lt_trichotomy kw k' with h | rfl | h
            · exact h
            · rw [hkw] at hr'
              cases hr'
              obtain ⟨-, p, -, hact, -⟩ := hch.okPoll hkw hww
              rw [ha'] at hact
              cases hact
            · exact absurd ⟨k', kw, r', w, hr', hid', hkw, hwid, h⟩
                (R.not_before_empty hX (a := 0) hy' (n := t + 1) (by omega) (by omega))
          omega
        · subst hyb
          have := ObjectInit.checked_record_index_eq hch hr' hx (hid'.trans hyid.symm)
          omega)
    have hc := MbarRing.Round.card_lt_of_uses T (Q := t + 1)
      (fun y hy => (Finset.mem_filter.mp hy).2.1) (z := (b, t)) (by simp)
      (fun h => (Finset.mem_filter.mp h).2.2 rfl)
    simp only [Fintype.card_fin] at hc
    have : 256 * s.phase < 256 * (t + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  simp [phaseAt, hsE, show s.phase = t by omega]

/-- **A consumer's poll acquires an earlier MMA.** An MMA of buffer `j`'s producer, with at most
`q` commits to the buffer's full barrier up to it, is acquired by a successful full poll of
consumer `b` at or before its successful poll with `q` earlier successful polls: among the first
`q + 1` notifications before that poll, of distinct commits, one is of a commit after the MMA. -/
theorem mma_observed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {km : Nat}
    (hR : X.TcAsync (producer L X c j, km)) {jw pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hew : X.get (consumerOf L c j b, jw) =
      some ⟨pc, .wait ((slot L c j).full ((slot L c j).owner b)) p true acq sc⟩) {q : Nat}
    (hq : okPolls ((slot L c j).full ((slot L c j).owner b))
      ((X.tr (consumerOf L c j b)).take jw) = q)
    (hK : ((X.tr (producer L X c j)).take (km + 1)).countP
      (commitsTo ((slot L c j).full 0)) ≤ q) :
    ∃ jw', jw' ≤ jw ∧ ∃ ws, AsyncObserved X (producer L X c j, km) .mmaDone
      (consumerOf L c j b, jw') true ws ∧
      ScopesMeet L .cluster (producer L X c j) ws (consumerOf L c j b) := by
  classical
  set F := (slot L c j).full ((slot L c j).owner b) with hF
  obtain ⟨jr, w, hjr, hwid, hwf, hww, hobs, hfl⟩ := cons_poll hpre hX ht hew
  rw [hq] at hobs hfl
  obtain ⟨jN, xN, hxN, hxNn, hcN⟩ := MbarRing.Slot.exists_nth_countP isArrival
    (xs := (X.objects F).take jr) (c := q) hfl
  have hjN : jN < jr := by
    have := (List.getElem?_eq_some_iff.mp hxN).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hjN] at hxN
  rw [List.take_take, Nat.min_eq_left hjN.le] at hcN
  have hnd : (X.objects F).Nodup := List.Nodup.of_map _ (hX.tma.2.2.1 F).1.1
  have hNlen : (((X.objects F).take (jN + 1)).filter isArrival).length = q + 1 := by
    rw [← List.countP_eq_length_filter, List.take_add_one, hxN, List.countP_append]
    simp only [Option.toList_some, List.countP_singleton, hxNn, ↓reduceIte]
    omega
  have hNnd : (((X.objects F).take (jN + 1)).filter isArrival).Nodup :=
    (hnd.sublist (List.take_sublist _ _)).filter _
  let f : Record Ref → Nat := fun x => match x.id with
    | .async i _ => i.2
    | _ => 0
  have hlate : ∃ x ∈ ((X.objects F).take (jN + 1)).filter isArrival, km + 1 ≤ f x := by
    by_contra hno
    push Not at hno
    have hle := MbarRing.Slot.length_le_countP_take _ hNnd (X.tr (producer L X c j))
      (commitsTo ((slot L c j).full 0)) (km + 1) f ?_ ?_
    · omega
    · intro x hx
      obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
      obtain ⟨jc, pcc, sp, hid, hcm, hmb, -⟩ :=
        notify_commit hpre hX ht (List.mem_of_mem_take hxt) hxn
      have hfx : f x = jc := by simp only [f, hid]
      refine ⟨hno x hx, ?_⟩
      rw [hfx]
      change (X.get (producer L X c j, jc)).any _ = true
      rw [hcm]
      simp [commitsTo, hmb]
    · intro x hx y hy hxy
      obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
      obtain ⟨hyt, hyn⟩ := List.mem_filter.mp hy
      obtain ⟨jc, -, -, hid, -⟩ := notify_commit hpre hX ht (List.mem_of_mem_take hxt) hxn
      obtain ⟨jc', -, -, hid', -⟩ := notify_commit hpre hX ht (List.mem_of_mem_take hyt) hyn
      have h1 : f x = jc := by simp only [f, hid]
      have h2 : f y = jc' := by simp only [f, hid']
      rw [h1, h2] at hxy
      subst hxy
      exact hX.record_eq (List.mem_of_mem_take hxt) (List.mem_of_mem_take hyt) (hid.trans hid'.symm)
  obtain ⟨x, hx, hkx⟩ := hlate
  obtain ⟨hxt, hxn⟩ := List.mem_filter.mp hx
  obtain ⟨jc, pcc, sp, hid, hcm, hmb, htg⟩ :=
    notify_commit hpre hX ht (List.mem_of_mem_take hxt) hxn
  have hfx : f x = jc := by simp only [f, hid]
  rw [hfx] at hkx
  obtain ⟨ix, hix⟩ := List.getElem?_of_mem hxt
  have hixl : ix < jN + 1 := by
    have := (List.getElem?_eq_some_iff.mp hix).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hixl] at hix
  have hph := notify_phase hpre hX ht hix hxn
  have hxf : x.fault = none := ((isArrival_iff x).mp hxn).2
  set r := ((X.objects F).take ix).countP isArrival with hr
  have hrq : r ≤ q := by
    rw [← hcN]
    exact ((List.take_prefix_take_left (show ix ≤ jN by omega)).sublist).countP_le
  -- the consumer's poll that observes the notification's phase
  have hcount : r + 1 ≤ okPolls F ((X.tr (consumerOf L c j b)).take (jw + 1)) := by
    have htk : (X.tr (consumerOf L c j b)).take (jw + 1) =
        (X.tr (consumerOf L c j b)).take jw ++ [⟨pc, .wait F p true acq sc⟩] := by
      rw [List.take_add_one, show (X.tr (consumerOf L c j b))[jw]? = _ from hew]
      rfl
    rw [htk, okPolls_snoc, hq]
    simp [okPoll, sourceWaitSuccess]
    omega
  obtain ⟨jw', pcw, pw, acqw, scw, hjw', hew', hcw⟩ := MbarRing.Poll.exists_nth (X := X)
    (g := consumerOf L c j b) (k := jw + 1) (m := F) (n := r) hcount
  have hgc := Frame.lt_of_get hX hew'
  obtain ⟨dc, hσc⟩ := Frame.event_state ht.sound hX ht.tracked hew' (by simp)
  obtain ⟨hacqf, -⟩ := ht.sync_flags hgc hew' hσc
  obtain ⟨hacq_t, hsc_t⟩ := hacqf _ _ _ _ _ rfl
  subst hacq_t hsc_t
  obtain ⟨jr', w', hjr', hwid', hwf', hww', hobs', -⟩ := cons_poll hpre hX ht hew'
  rw [hcw] at hobs'
  have hxm := List.mem_of_getElem? hix
  have hobj : objectAction X X.async F
      (.async (producer L X c j, jc) (.tcNotify ⟨((slot L c j).owner b).val, by omega⟩)) =
        some x.action := by
    have h := ((hX.tma.2.2.1 _).2.1 x hxm).1
    rw [hid] at h
    exact h
  obtain ⟨-, -, -, -, hnotif⟩ := notify_facts hobj
  have hupd := MbarRing.Slot.updateBeforeWait_of_phase (hX.tma.2.2.1 _).1
      (objects_noInval hX ht _) hix hxf hjr' hwf' hww'
    hph hobs'
  rw [hid, hwid'] at hupd
  have hgp : producer L X c j < L.threads := Frame.lt_of_get hX hcm
  have hcl1 : (consumerOf L c j b) / L.block / 2 = c := by
    rw [consumerOf_div (by rw [hpre.block]; decide)]
    have := b.isLt
    omega
  have hcl2 : (producer L X c j) / L.block / 2 = c := by
    have h := producer_thread (X := X) hpre c j
    simp only [producerThread, decide_eq_true_eq] at h
    omega
  have hclu : L.clusterOfCta ((producer L X c j) / L.block) =
      L.clusterOfCta ((consumerOf L c j b) / L.block) := by
    simp only [clusterOfCta_eq hpre]
    omega
  exact ⟨jw', by omega, .cluster, ⟨_, F, ⟨(producer L X c j, jc), sp,
    ⟨((slot L c j).owner b).val, by omega⟩, rfl, ⟨rfl, by omega, hR, sp, ⟨pcc, hcm⟩⟩, ⟨pcc, hcm⟩,
    htg, hnotif⟩, ⟨⟨pcw, pw, hew'⟩, hupd⟩⟩, ⟨⟨hgp, hgc, hclu⟩, ⟨hgc, hgp, hclu.symm⟩⟩⟩


/-- **An MMA happens before a later tile's load.** An MMA of buffer `j`'s producer, with fewer
commits to the buffer's full barrier up to it than consumer `b`'s successful full polls before
an event `k'`, is observed complete before that event. -/
theorem mma_before_load (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {km k' : Nat}
    (hR : X.TcAsync (producer L X c j, km)) (hk' : k' < (X.tr (consumerOf L c j b)).length)
    (hle : ((X.tr (producer L X c j)).take (km + 1)).countP
        (commitsTo ((slot L c j).full 0)) + 1 ≤
      okPolls ((slot L c j).full ((slot L c j).owner b)) ((X.tr (consumerOf L c j b)).take k')) :
    TcMma.DoneBefore L X (producer L X c j, km) (consumerOf L c j b, k') := by
  obtain ⟨jw, pc, p, acq, sc, hjw, hew, hcw⟩ := MbarRing.Poll.exists_nth (X := X)
    (g := consumerOf L c j b) (k := k') hle
  obtain ⟨jw', hjw', ws, hobs, hsc⟩ := mma_observed hpre hX ht hR hew hcw le_rfl
  exact .inl ⟨_, ws, hobs, hsc,
    Relation.TransGen.single (Or.inl (po_of_source_not_access rfl (by simp only; omega) hk'
    hobs.not_access))⟩

/-- **A load happens before a later batch's MMA.** A Tensor Memory load of consumer `b`, followed
by its wait, is finished before an event of buffer `j`'s producer that has polled the empty
barrier successfully at least two more times than `b`'s arrivals there before the load: the
producer's poll observing phase `q` (`q` those arrivals) acquires `b`'s arrival of phase `q`,
which follows the load's wait. -/
theorem load_before_mma (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {k' km pcl a : Nat}
    {vals : List Value}
    (hld : X.get (consumerOf L c j b, k') = some ⟨pcl, .tc (.ld a vals .s32x32b)⟩)
    (hwait : k' + 1 < (X.tr (consumerOf L c j b)).length → X.WaitLd (consumerOf L c j b, k' + 1))
    (hkm : km < (X.tr (producer L X c j)).length)
    (hcnt : arrivals ((slot L c j).empty 0) ((X.tr (consumerOf L c j b)).take k') + 2 ≤
      okPolls ((slot L c j).empty 0) ((X.tr (producer L X c j)).take km)) :
    TcMma.WaitBefore L X .waitLd (consumerOf L c j b, k') (producer L X c j, km) := by
  have hblock := hpre.block
  set q := arrivals ((slot L c j).empty 0) ((X.tr (consumerOf L c j b)).take k') with hq
  obtain ⟨jl, pcw, pw, acqw, scw, hjl, hwl, hcl⟩ := MbarRing.Poll.exists_nth (X := X)
    (g := producer L X c j) (k := km) (m := (slot L c j).empty 0) (n := q + 1) (by omega)
  obtain ⟨jr, w, hjr, hwid, hwf, hww, hobs, hnot⟩ := prod_poll hpre hX ht hwl hcl
  obtain ⟨jN, x, hx, hxn, hcN⟩ :=
    MbarRing.Slot.exists_nth_countP ((slot L c j).notification 0 b)
    (xs := (X.objects ((slot L c j).empty 0)).take jr) (c := q) (hnot b)
  have hjN : jN < jr := by
    have := (List.getElem?_eq_some_iff.mp hx).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hjN] at hx
  rw [List.take_take, Nat.min_eq_left hjN.le] at hcN
  obtain ⟨hxf, hph⟩ := arrive_phase hpre hX ht hx hxn
  rw [hcN] at hph
  obtain ⟨ja, pca, tx, cnt, sca, hid, hea, rfl, hacnt⟩ := arrive_record hX ht hx hxn
  rw [hcN] at hacnt
  -- the arrival follows the load
  have hja : k' < ja := by
    by_contra hle
    rcases Nat.lt_or_ge ja k' with hlt | hge
    · have h1 : arrivals ((slot L c j).empty 0) ((X.tr (consumerOf L c j b)).take (ja + 1)) =
          q + 1 := by
        rw [List.take_add_one, show (X.tr (consumerOf L c j b))[ja]? = _ from hea]
        simp only [Option.toList_some, arrivals, List.countP_append]
        rw [show List.countP (arrivesOn ((slot L c j).empty 0)) _ = q from hacnt]
        simp [arrivesOn, sourceArrive]
      have h2 : arrivals ((slot L c j).empty 0) ((X.tr (consumerOf L c j b)).take (ja + 1)) ≤ q :=
        ((List.take_prefix_take_left (show ja + 1 ≤ k' by omega)).sublist).countP_le
      omega
    · have : ja = k' := by omega
      subst this
      rw [hld] at hea
      cases hea
  have hjal : ja < (X.tr (consumerOf L c j b)).length := len_of_get hea
  have hw := hwait (by omega)
  -- the producer's acquire
  have hgp := Frame.lt_of_get hX hwl
  obtain ⟨dw, hσw⟩ := Frame.event_state ht.sound hX ht.tracked hwl (by simp)
  obtain ⟨hacqt, hacqs⟩ := (ht.sync_flags hgp hwl hσw).1 _ _ _ _ _ rfl
  subst hacqt hacqs
  have hupd := MbarRing.Slot.updateBeforeWait_of_phase (hX.tma.2.2.1 _).1
      (objects_noInval hX ht _) hx hxf hjr hwf hww hph hobs
  rw [hid, hwid] at hupd
  have hgc := Frame.lt_of_get hX hea
  have hcl1 : (consumerOf L c j b) / L.block / 2 = c := by
    rw [consumerOf_div (by omega)]
    have := b.isLt
    omega
  have hcl2 : (producer L X c j) / L.block / 2 = c := by
    have h := producer_thread (X := X) hpre c j
    simp only [producerThread, decide_eq_true_eq] at h
    omega
  have hclu : L.clusterOfCta ((consumerOf L c j b) / L.block) =
      L.clusterOfCta ((producer L X c j) / L.block) := by
    simp only [clusterOfCta_eq hpre]
    omega
  have hms : MSync L X (consumerOf L c j b, k' + 1) (producer L X c j, km) :=
    ⟨(consumerOf L c j b, ja), (producer L X c j, jl), (slot L c j).empty 0, .cluster, .cluster,
      ⟨tx, cnt, pca, hea⟩, ⟨⟨pcw, pw, hwl⟩, hupd⟩, ⟨⟨hgc, hgp, hclu⟩, ⟨hgp, hgc, hclu.symm⟩⟩, rfl,
      hjl, hkm, rfl, by simp only; omega⟩
  exact ⟨_, hw, rfl, by simp, .inl (Relation.TransGen.single (Or.inr (Or.inr (Or.inl hms))))⟩


end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
