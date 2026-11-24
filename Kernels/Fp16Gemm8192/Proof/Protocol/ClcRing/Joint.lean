-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Ring

@[expose] public section

/-! # The CLC response ring's phases and fault freedom

From the ring of items (`ring`) and each object's own history:

* consumer `b`'s successful response poll with `j` earlier ones found phase `j + 1`
  (`fpoll_phase`): at least by the parity of its polls, at most by the completions before it,
  which are of uses at most `j` (`not_before_full`);
* a completion of response barrier `f` is the completion of the request numbered by the
  completions before it, in the phase of that number (`completion_ordinal`);
* the leader's acknowledgement poll with `n ≥ 1` earlier ones found phase `n`
  (`epoll_phase`, `empty_poll_phase`);
* every record of the response and acknowledgement barriers is fault-free (`clcFacts`): the
  initialization is the first record, polls follow it, a scheduler's arrival numbered `s` is in
  phase `s` after its poll that found phase `s`, a completion leaves the transaction counter
  in range, and an acknowledgement numbered `t` has fewer than ten times `t + 1` units before
  it and follows the leader's polls that found the phases `1, …, t`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A successful completion record. -/
abbrev isDone (r : Record Ref) : Bool :=
  match r.action, r.fault with | .completeTx _, none => true | _, _ => false

theorem isDone_iff {r : Record Ref} : isDone r = true ↔ r.fault = none ∧ ∃ n, r.action =
    .completeTx n := by
  unfold isDone
  cases ha : r.action <;> cases hf : r.fault <;> simp

/-- The loader of CTA `f`, a consumer of response barrier `f`. -/
def ownerB (f : Fin 2) : Fin 10 := ⟨f.val, by have := f.isLt; omega⟩

theorem owner_ownerB (L : Launch) (c : Nat) (f : Fin 2) : (slot L c).owner (ownerB f) = f := by
  fin_cases f <;> rfl

/-- **The phase of a consumer's response poll.** Consumer `b`'s successful poll with `j` earlier
ones found phase `j + 1`, so it observed phase `j`. -/
theorem fpoll_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {j : Nat}
    (hp : X.RefPresent (.thread (fpoll L X c b j))) :
    ∃ i w st, (X.objects ((slot L c).full ((slot L c).owner b)))[i]? = some w ∧
      w.id = .thread (fpoll L X c b j) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects ((slot L c).full ((slot L c).owner b))) i = some st ∧
      st.phase = j + 1 ∧ oF L X c b j = j ∧
      observedAt (X.objects ((slot L c).full ((slot L c).owner b))) i = some j := by
  classical
  obtain ⟨i, w, st, hi, hwid, hww, hsel, hst, hpos, ho, hoi⟩ := fpoll_rec hpre hX ht hp
  have hch := (hX.tma.2.2.1 ((slot L c).full ((slot L c).owner b))).1
  have hni := objects_noInval hX ht ((slot L c).full ((slot L c).owner b))
  obtain ⟨st', hst', hge, -⟩ := hch.selected_poll_phase_ge hni (objectThreadSelected (thr L X c b))
    (δ := 0) (by omega) (resp_alt hpre hX ht _ (2 * c + ((slot L c).owner b).val)) hi
    (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww
  rw [hst] at hst'
  cases hst'
  have hil : i ≤ (X.objects ((slot L c).full ((slot L c).owner b))).length :=
    (List.getElem?_eq_some_iff.mp hi).1.le
  have hle : st.phase ≤
      completedTxCount ((X.objects ((slot L c).full ((slot L c).owner b))).take i) :=
    (resp_unitTx hpre hX ht (2 * c + ((slot L c).owner b).val)).phase_le_completed
      (by norm_num) hch hni hil hst
  have hcnt : completedTxCount ((X.objects ((slot L c).full ((slot L c).owner b))).take i) ≤
      j + 1 := by
    have h := countP_take_le_card hch.1 isDone (i := i)
      ((Finset.range (j + 1)).image (item L X c ((slot L c).owner b))) (fun k hk r hr hd => by
        obtain ⟨hf, n, ha⟩ := isDone_iff.mp hd
        obtain ⟨s, hid⟩ := item_of_completion hpre hX ht (List.mem_of_getElem? hr) ha
        have hx : ((0 : Fin 1), s) ∈ SF L X c ((slot L c).owner b) :=
          (mem_SF hX).mpr ⟨r, List.mem_of_getElem? hr, hid, hf⟩
        refine Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr ?_, hid.symm⟩
        by_contra hgt
        exact (ring hpre hX ht c).not_before_full hX (m := (slot L c).full ((slot L c).owner b))
          hx (b := b) (j := j) (by simp; omega) ⟨k, i, r, w, hr, hid, hi, hwid, hk⟩)
    exact h.trans (Finset.card_image_le.trans (by simp))
  have hph : st.phase = j + 1 := by
    rw [hsel] at hge
    omega
  refine ⟨i, w, st, hi, hwid, hww, hst, hph, ?_, ?_⟩
  · rw [ho, hph]; rfl
  · rw [hoi, hph]; rfl

/-- The phase of a selected reader's successful response poll is one more than its earlier
successful polls. -/
theorem sel_poll_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g k pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hsel : consumerSel L c b g = true)
    (he : X.get (g, k) = some ⟨pc, .wait ((slot L c).full ((slot L c).owner b)) p true acq sc⟩) :
    ∃ i w st, (X.objects ((slot L c).full ((slot L c).owner b)))[i]? = some w ∧
      w.id = .thread (g, k) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects ((slot L c).full ((slot L c).owner b))) i = some st ∧
      st.phase = okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr g).take k) + 1 ∧
      observedAt (X.objects ((slot L c).full ((slot L c).owner b))) i =
        some (okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr g).take k)) := by
  have hg := thr_eq hpre hX ht hsel he
  subst hg
  have hk := MbarRing.Poll.nth_eq he
  obtain ⟨i, w, st, hi, hwid, hww, hst, hph, -, ho⟩ := fpoll_phase hpre hX ht (c := c) (b := b)
    (j := okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr (thr L X c b)).take k))
    (by rw [show fpoll L X c b _ = (thr L X c b, k) by simp only [fpoll, hk]]; exact ⟨_, he⟩)
  refine ⟨i, w, st, hi, ?_, hww, hst, hph, ho⟩
  rw [hwid]
  simp only [fpoll, hk]

/-- **The ordinal of a completion.** A non-faulting completion of response barrier `f` is the
completion of the request numbered by the completions before it, which is also its phase. -/
theorem completion_ordinal (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {jd : Nat} {d : Record Ref}
    (hd : (X.objects ((slot L c).full f))[jd]? = some d) (hdf : d.fault = none) {n : Nat}
    (ha : d.action = .completeTx n) :
    ∃ s, d.id = item L X c f s ∧ phaseAt (X.objects ((slot L c).full f)) jd = some s ∧
      completedTxCount ((X.objects ((slot L c).full f)).take jd) = s := by
  classical
  have hacyc := hX.depAcyclic
  set R := ring hpre hX ht c with hR
  have hch := (hX.tma.2.2.1 ((slot L c).full f)).1
  have hni := objects_noInval hX ht ((slot L c).full f)
  obtain ⟨s, hid⟩ := item_of_completion hpre hX ht (List.mem_of_getElem? hd) ha
  have hx : ((0 : Fin 1), s) ∈ SF L X c f := (mem_SF hX).mpr ⟨d, List.mem_of_getElem? hd, hid, hdf⟩
  have hjd0 := ring_pos (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hd
    (by rw [ha]; intro m h; cases h)
  obtain ⟨st, hst⟩ := ring_state_at (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hd hjd0
  have hst : stateBefore (X.objects ((slot L c).full f)) jd = some st := hst
  have hjdl : jd < (X.objects ((slot L c).full f)).length := (List.getElem?_eq_some_iff.mp hd).1
  have hown := owner_ownerB L c f
  -- the poll of the loader of CTA `f` with `j` earlier ones, present: its record before an item
  -- of a later use, in phase `j + 1`
  have poll_before : ∀ j s' (hx' : ((0 : Fin 1), s') ∈ SF L X c f) (k : Nat) (r : Record Ref),
      j < s' → (X.objects ((slot L c).full f))[k]? = some r → r.id = item L X c f s' →
      ∃ st', stateBefore (X.objects ((slot L c).full f)) k = some st' ∧ j + 1 ≤ st'.phase := by
    intro j s' hx' k r hjs hk hrid
    obtain ⟨hpres, -⟩ := R.reach_op hacyc (fun n h1 hn => R.guardP f _ hx' n h1 hn)
      (ownerB f) hjs
    obtain ⟨i, w, st1, hi, hwid, -, hst1, hph1, -, -⟩ := fpoll_phase hpre hX ht hpres
    rw [hown] at hi hst1
    have hik : i < k := by
      rcases Nat.lt_or_ge i k with h | h
      · exact h
      · rcases Nat.lt_or_eq_of_le h with h | rfl
        · exact absurd ⟨k, i, r, w, hk, hrid, hi, hwid, h⟩
            (R.not_before_full hX (m := (slot L c).full f) hx' (b := ownerB f) (j := j) hjs)
        · rw [hk] at hi
          cases hi
          rw [hrid] at hwid
          cases hwid
    obtain ⟨t, ht', hle⟩ := hch.phase_mono hni hik.le (List.getElem?_eq_some_iff.mp hk).1.le hst1
    exact ⟨t, ht', by omega⟩
  -- lower bound: the loader's poll for use `s - 1` found phase `s`
  have hlow : s ≤ st.phase := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · omega
    obtain ⟨st', hst', hle⟩ := poll_before (s - 1) s hx jd d (by omega) hd hid
    rw [hst] at hst'
    cases hst'
    omega
  -- if a later item exists, the loader's poll for use `s` observed this item, in phase `s`
  have hlater : ∀ s', ((0 : Fin 1), s') ∈ SF L X c f → s < s' → st.phase = s := by
    intro s' hx' hss
    obtain ⟨hpres, -⟩ := R.reach_op hacyc (fun n h1 hn => R.guardP f _ hx' n h1 hn)
      (ownerB f) hss
    obtain ⟨-, -, -, -, -, -, -, -, hoF, -⟩ := fpoll_phase hpre hX ht hpres
    obtain ⟨-, hphF⟩ := (R.content_full hacyc hpres).2 0
    have h1 := MbarRing.Poll.phaseOf_eq hX hd (show phaseAt _ jd = some st.phase by
      simp [phaseAt, hst])
    rw [hid] at h1
    have : phF L X c f (0, s) = oF L X c (ownerB f) s := by
      have := hphF
      simp only [hR, ring] at this
      rw [hown] at this
      exact this
    simp only [phF] at this
    rw [h1, hoF] at this
    exact this
  -- the completions before it are of earlier uses
  have hcnt : completedTxCount ((X.objects ((slot L c).full f)).take jd) ≤ s := by
    have h := countP_take_le_card hch.1 isDone (i := jd)
      ((Finset.range s).image (item L X c f)) (fun k hk r hr hdn => by
        obtain ⟨hf, m, ham⟩ := isDone_iff.mp hdn
        obtain ⟨s', hid'⟩ := item_of_completion hpre hX ht (List.mem_of_getElem? hr) ham
        have hx' : ((0 : Fin 1), s') ∈ SF L X c f :=
          (mem_SF hX).mpr ⟨r, List.mem_of_getElem? hr, hid', hf⟩
        refine Finset.mem_image.mpr ⟨s', Finset.mem_range.mpr ?_, hid'.symm⟩
        rcases Nat.lt_trichotomy s' s with h | rfl | h
        · exact h
        · have := ObjectInit.checked_record_index_eq hch hr hd (hid'.trans hid.symm)
          omega
        · exfalso
          have hph := hlater s' hx' h
          obtain ⟨st', hst', hle⟩ := poll_before s s' hx' k r h hr hid'
          obtain ⟨t, ht', hle'⟩ := hch.phase_mono hni hk.le hjdl.le hst'
          rw [hst] at ht'
          cases ht'
          omega)
    exact h.trans (Finset.card_image_le.trans (by simp))
  have hup : st.phase ≤ completedTxCount ((X.objects ((slot L c).full f)).take jd) :=
    (resp_unitTx hpre hX ht (2 * c + f.val)).phase_le_completed (by norm_num) hch hni hjdl.le hst
  refine ⟨s, hid, ?_, by omega⟩
  simp only [phaseAt, hst, Option.map_some]
  congr 1
  omega

/-- At any position of a response barrier, the completions before it are at most one more than
its phase: each is in the phase of its number. -/
theorem completions_le_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {i : Nat} {st : State}
    (hst : stateBefore (X.objects ((slot L c).full f)) i = some st) :
    completedTxCount ((X.objects ((slot L c).full f)).take i) ≤ st.phase + 1 := by
  classical
  have hch := (hX.tma.2.2.1 ((slot L c).full f)).1
  have hni := objects_noInval hX ht ((slot L c).full f)
  have hil := (stateBefore_lt hst).2
  have h := countP_take_le_card hch.1 isDone (i := i)
    ((Finset.range (st.phase + 1)).image (item L X c f)) (fun k hk r hr hdn => by
      obtain ⟨hf, m, ham⟩ := isDone_iff.mp hdn
      obtain ⟨s, hid, hph, -⟩ := completion_ordinal hpre hX ht hr hf ham
      refine Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr ?_, hid.symm⟩
      have := hch.phaseAt_le hni hil hk.le hst hph
      omega)
  exact h.trans (Finset.card_image_le.trans (by simp))

/-- Every non-faulting arrival on the acknowledgement barrier is a counted unit
acknowledgement. -/
theorem ack_count (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} :
    ∀ (k : Nat) (r : Record Ref) (n tx : Nat), (X.objects ((slot L c).empty 0))[k]? = some r →
      r.fault = none → r.action = .arrive n tx →
      n = 1 ∧ ∃ y ∈ SE L X c, r.id = .thread (ackEv L X c y.1 y.2) := by
  intro k r n tx hk hf ha
  have hr := List.mem_of_getElem? hk
  obtain ⟨b, t, hid⟩ := ack_of_arrival hpre hX ht hr ha
  refine ⟨?_, (b, t), (mem_SE hX).mpr ⟨r, hr, hid, hf⟩, hid⟩
  cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos hr with
  | arrive _ _ ha' => rw [ha] at ha'; cases ha'; rfl
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
  | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
  | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby

/-- **The phase of the leader's acknowledgement poll.** Its successful poll with `n ≥ 1` earlier
ones found phase `n`, so it observed phase `n - 1`. -/
theorem epoll_phase (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c n : Nat} (hn1 : 1 ≤ n)
    (hp : X.RefPresent (.thread (epoll L X c n))) :
    ∃ i w st, (X.objects ((slot L c).empty 0))[i]? = some w ∧
      w.id = .thread (epoll L X c n) ∧ w.reply.waited = some true ∧
      stateBefore (X.objects ((slot L c).empty 0)) i = some st ∧ st.phase = n ∧
      observedAt (X.objects ((slot L c).empty 0)) i = some (n - 1) := by
  obtain ⟨i, w, st, hi, hwid, hww, hsel, hst, hpos, -, hoi⟩ := epoll_rec hpre hX ht hn1 hp
  obtain ⟨st', hst', hph⟩ := (ring hpre hX ht c).empty_poll_phase hX (by norm_num)
      (objects_noInval hX ht _) (a := 0)
    (objectThreadSelected (producer L X c)) (δ := 1) le_rfl (ack_alt hpre hX ht _ (2 * c))
    (ack_count hpre hX ht) (fun k s hs => ring_expected (b := ⟨.clc, 0, false⟩) hpre hX ht
      Nat.one_pos hs) hn1 hi hwid hww (objectThreadSelected_iff.mpr ⟨_, hwid⟩)
      (hsel.trans (by omega))
  have hst'' : stateBefore (X.objects ((slot L c).empty 0)) i = some st' := hst'
  rw [hst] at hst''
  cases hst''
  exact ⟨i, w, st, hi, hwid, hww, hst, hph, by rw [hoi, hph]⟩

/-! ### Fault freedom -/

/-- The initialization of a ring barrier is its first record, which does not fault. -/
theorem init_ok (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} (hb : b.Valid) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (b.loc L cta)) {n : Nat} (ha : r.action = .init n) : r.fault = none := by
  obtain ⟨r0, h0, hid0, -, hf0⟩ := first_record hpre hX ht hb hr
  obtain ⟨hid, -, -⟩ := init_source hX ht hb hr ha
  rw [hX.record_eq hr (List.mem_of_getElem? h0) (hid.trans hid0.symm)]
  exact hf0

/-- The arrivals on a response barrier are its CTA's scheduler's. -/
theorem resp_arrival (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {f : Fin 2} {r : Record Ref} (hr : r ∈ X.objects ((slot L c).full f)) {n tx : Nat}
    (ha : r.action = .arrive n tx) :
    ∃ g jj pc rel sc d, r.id = .thread (g, jj) ∧
      X.get (g, jj) = some ⟨pc, .arrive ((slot L c).full f) 16 1 rel sc⟩ ∧ n = 1 ∧ tx = 16 ∧
      consumerSel L c ⟨2 + f.val, by have := f.isLt; omega⟩ g = true ∧
      Frame.stateAt (code L) X g jj = some (some (.inr (.sched d))) := by
  cases bar_source (b := ⟨.clc, 0, true⟩) hX ht Nat.one_pos hr with
  | @arrive g jj pc rel sc d hid he ha' hσ hby hcta =>
    rw [ha] at ha'
    cases ha'
    obtain ⟨sd, rfl⟩ := hby
    simp only [Bar.arriveCta, Bar.arriveLeader, Bool.false_eq_true, ↓reduceIte] at hcta
    have hg := Frame.lt_of_get hX he
    have hw := ht.role_warp hg (idx_le he) hσ
    simp only [roleWarp] at hw
    refine ⟨g, jj, pc, rel, sc, sd, hid, he, rfl, rfl, ?_, hσ⟩
    simp only [consumerSel, decide_eq_true_eq]
    have hf := f.isLt
    rcases (by omega : f.val = 0 ∨ f.val = 1) with h | h <;> simp only [h] <;>
      simp [ctaOf, warpOf, laneZero] <;> omega
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
  | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
  | clc _ _ _ ha' => rw [ha] at ha'; cases ha'

/-- **A scheduler's arrival on its response barrier does not fault.** Its arrival numbered `s`
has at most `s` arrival units before it, all its own, and follows its own successful poll that
found phase `s`: it is in phase `s`, with its arrival pending and the phase observed, and the
transaction counter in range. -/
theorem resp_arrive_ok (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {i : Nat} {r : Record Ref}
    (hi : (X.objects ((slot L c).full f))[i]? = some r) {n tx : Nat}
    (ha : r.action = .arrive n tx) : r.fault = none := by
  have hr := List.mem_of_getElem? hi
  have hch := (hX.tma.2.2.1 ((slot L c).full f)).1
  have hni := objects_noInval hX ht ((slot L c).full f)
  obtain ⟨g, jj, pc, rel, sc, sd, hid, he, rfl, rfl, hsel, hσ⟩ := resp_arrival hX ht hr ha
  have hg := Frame.lt_of_get hX he
  set s := arrivals ((slot L c).full f) ((X.tr g).take jj) with hs
  obtain ⟨st, hst⟩ := ring_state_at (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hi
    (ring_pos (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hi (by rw [ha]; intro m h; cases h))
  have hst : stateBefore (X.objects ((slot L c).full f)) i = some st := hst
  have hil : i ≤ (X.objects ((slot L c).full f)).length := (List.getElem?_eq_some_iff.mp hi).1.le
  have hu : UnitTx (X.objects ((slot L c).full f)) 16 := resp_unitTx hpre hX ht (2 * c + f.val)
  obtain ⟨hpend, hunits⟩ := hu.units hch hni hil hst
  -- the arrival units before it are its own earlier arrivals
  have hA : unitsBefore (X.objects ((slot L c).full f)) i ≤ s := by
    have h1 := arrivalUnits_le_countP (xs := (X.objects ((slot L c).full f)).take i)
      (threadArrival g) (fun q hq hqf c' tx' hqa => by
        obtain ⟨g', jj', _, _, _, _, hqid, hqe, rfl, rfl, hsel', hσ'⟩ :=
          resp_arrival hX ht (List.mem_of_mem_take hq) hqa
        have hgg : g' = g := sel_eq hpre hX ht hsel hsel' he hqe
          ⟨_, hσ, ht.role_warp hg (idx_le he) hσ⟩ trivial trivial
          ⟨_, hσ', ht.role_warp (Frame.lt_of_get hX hqe) (idx_le hqe) hσ'⟩
        subst hgg
        exact ⟨rfl, threadArrival_iff.mpr ⟨objectThreadSelected_iff.mpr ⟨_, hqid⟩, _, _, hqa⟩⟩)
    have h2 := hX.object_thread_arrival_count_window (m := (slot L c).full f) (g := g) (k := jj)
      ((X.objects ((slot L c).full f)).take i) (fun _ hq => List.mem_of_mem_take hq)
      (hch.1.sublist ((List.take_sublist i _).map _))
      (fun q j hq hqid => hX.object_thread_take_mem_iff hi hid hq hqid)
    unfold unitsBefore
    rw [h2] at h1
    exact h1
  -- the phase is `s`, after its own poll that found phase `s`
  have hlow : s ≤ st.phase ∧ (st.phase = 0 ∨ ∃ k w sk, k < i ∧
      (X.objects ((slot L c).full f))[k]? = some w ∧ w.reply.waited = some true ∧
      stateBefore (X.objects ((slot L c).full f)) k = some sk ∧ sk.phase = st.phase) := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · have : st.phase = 0 := by omega
      exact ⟨by omega, .inl this⟩
    obtain ⟨d, hσd⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    have hab := ht.arrival_budget (b := ⟨.clc, 0, true⟩) (cta := 2 * c + f.val) hg he hσd rfl
      Nat.one_pos
    have hloc : (Bar.gate ⟨.clc, 0, true⟩).loc L (g / L.block) = (slot L c).full f := by
      have hcf : ctaOf ⟨2 + f.val, by have := f.isLt; omega⟩ = f.val := by fin_cases f <;> rfl
      rw [sel_cta hsel, hcf]
      rfl
    rw [hloc] at hab
    simp only [Bar.gateSlack, Nat.add_zero] at hab
    have hab' : s ≤ okPolls ((slot L c).full f) ((X.tr g).take jj) := hab
    obtain ⟨w, pcw, pw, acqw, scw, hwj, hew, hcw⟩ :=
      MbarRing.Poll.exists_nth (X := X) (g := g) (k := jj) (m := (slot L c).full f)
        (n := s - 1) (by omega)
    have hown : (slot L c).owner ⟨2 + f.val, by have := f.isLt; omega⟩ = f := by
      fin_cases f <;> rfl
    obtain ⟨i', w', st', hi', hwid', hww', hst', hph', -⟩ := sel_poll_phase hpre hX ht hsel
      (by rw [hown]; exact hew)
    rw [hown] at hi' hst' hph'
    rw [hcw] at hph'
    have hii : i' < i := (hX.object_thread_index_iff hi' hi hwid' hid).mpr hwj
    obtain ⟨t, ht', hle⟩ := hch.phase_mono hni hii.le hil hst'
    rw [hst] at ht'
    cases ht'
    have : st.phase = s := by omega
    exact ⟨by omega, .inr ⟨i', w', st', hii, hi', hww', hst', by omega⟩⟩
  have hobs := hch.observed_of_poll hni hst hlow.2
  have hcl := hu.phase_le_completed (by norm_num) hch hni hil hst
  have hcu := completions_le_phase hpre hX ht hst
  have htx := hu.tx hch hni hil hst
  have hok : RecordOk (some st) r := hst ▸ hch.at hi
  refine RecordOk.arrive_fault_none hok ha (by decide) (by decide) hobs (by omega) ?_
  simp only [validTx, limit]
  constructor <;> omega

/-- **A completion of a response barrier does not fault**: the transaction counter stays in
range, the completions so far being the phase or one more and the arrivals the phase or one
more. -/
theorem resp_complete_ok (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {i : Nat} {r : Record Ref}
    (hi : (X.objects ((slot L c).full f))[i]? = some r) {n : Nat}
    (ha : r.action = .completeTx n) : r.fault = none := by
  have hr := List.mem_of_getElem? hi
  have hch := (hX.tma.2.2.1 ((slot L c).full f)).1
  have hni := objects_noInval hX ht ((slot L c).full f)
  have hn : n = 16 := by
    cases bar_source (b := ⟨.clc, 0, true⟩) hX ht Nat.one_pos hr with
    | clc _ _ _ ha' => rw [ha] at ha'; cases ha'; rfl
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | arrive _ _ ha' => rw [ha] at ha'; cases ha'
    | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
    | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
  subst hn
  obtain ⟨st, hst⟩ := ring_state_at (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hi
    (ring_pos (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hi (by rw [ha]; intro m h; cases h))
  have hst : stateBefore (X.objects ((slot L c).full f)) i = some st := hst
  have hil : i ≤ (X.objects ((slot L c).full f)).length := (List.getElem?_eq_some_iff.mp hi).1.le
  have hu : UnitTx (X.objects ((slot L c).full f)) 16 := resp_unitTx hpre hX ht (2 * c + f.val)
  obtain ⟨hpend, hunits⟩ := hu.units hch hni hil hst
  rw [incrementsBefore_eq_zero _ (incrementsBefore_zero hX ht _)] at hpend hunits
  have hcl := hu.phase_le_completed (by norm_num) hch hni hil hst
  have hcu := completions_le_phase hpre hX ht hst
  have htx := hu.tx hch hni hil hst
  have hok : RecordOk (some st) r := hst ▸ hch.at hi
  refine RecordOk.complete_fault_none hok ha (by decide) ?_
  simp only [validTx, limit]
  constructor <;> omega

/-- The acknowledgement barrier's transaction counter stays zero: its arrivals expect no bytes
and nothing completes on it. -/
theorem ack_tx (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c i : Nat} {st : State}
    (hst : stateBefore (X.objects ((slot L c).empty 0)) i = some st) : st.tx = 0 := by
  have hch := (hX.tma.2.2.1 ((slot L c).empty 0)).1
  have hni := objects_noInval hX ht ((slot L c).empty 0)
  have hil := (stateBefore_lt hst).2
  rw [hch.tx_balance hni hil hst]
  have h1 : expectedTxBytes ((X.objects ((slot L c).empty 0)).take i) =
      0 * arrivalUnits ((X.objects ((slot L c).empty 0)).take i) :=
    expectedTxBytes_unit fun q hq _ c' tx' hqa => by
      cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos (List.mem_of_mem_take hq) with
      | arrive _ _ ha' => rw [hqa] at ha'; cases ha'; exact ⟨rfl, rfl⟩
      | init ha' => rw [hqa] at ha'; cases ha'
      | poll _ _ ha' => rw [hqa] at ha'; cases ha'
      | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
      | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
      | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby
  have h2 : completedTxBytes ((X.objects ((slot L c).empty 0)).take i) =
      0 * completedTxCount ((X.objects ((slot L c).empty 0)).take i) :=
    completedTxBytes_eq_unit_mul_count fun q hq _ m hqa => by
      cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos (List.mem_of_mem_take hq) with
      | arrive _ _ ha' => rw [hqa] at ha'; cases ha'
      | init ha' => rw [hqa] at ha'; cases ha'
      | poll _ _ ha' => rw [hqa] at ha'; cases ha'
      | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
      | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
      | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby
  rw [h1, h2]
  simp

/-- **An acknowledgement does not fault.** Consumer `b`'s acknowledgement numbered `t`, if not
counted, leaves every counted acknowledgement at a use at most `t` (a later one needs the
leader's poll for use `t + 1`, which observed this one), so fewer than `10 (t + 1)` units
precede it; and the leader's polls for the uses `1, …, t`, which found the phases `1, …, t`,
precede it (`reach_consumer_op`). The transaction counter of the barrier stays zero. -/
theorem ack_ok (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c i : Nat} {r : Record Ref}
    (hi : (X.objects ((slot L c).empty 0))[i]? = some r) {n tx : Nat}
    (ha : r.action = .arrive n tx) : r.fault = none := by
  classical
  have hacyc := hX.depAcyclic
  set R := ring hpre hX ht c with hR
  have hr := List.mem_of_getElem? hi
  have hch := (hX.tma.2.2.1 ((slot L c).empty 0)).1
  have hni := objects_noInval hX ht ((slot L c).empty 0)
  have ha1 : r.action = .arrive 1 0 := by
    cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos hr with
    | arrive _ _ ha' => exact ha'
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
    | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
    | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby
  obtain ⟨b, t, hid⟩ := ack_of_arrival hpre hX ht hr ha
  obtain ⟨ev, he⟩ : X.RefPresent (.thread (ackEv L X c b t)) :=
    hid ▸ object_record_present hX.tma hr
  obtain ⟨st, hst⟩ := ring_state_at (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hi
    (ring_pos (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hi (by rw [ha]; intro m h; cases h))
  have hst : stateBefore (X.objects ((slot L c).empty 0)) i = some st := hst
  have hil : i ≤ (X.objects ((slot L c).empty 0)).length := (List.getElem?_eq_some_iff.mp hi).1.le
  have htx : st.tx = 0 := ack_tx hX ht hst
  have hok : RecordOk (some st) r := hst ▸ hch.at hi
  by_contra hf
  have hnot : (b, t) ∉ SE L X c := fun hm => hf (by
    obtain ⟨r', hr', hid', hf'⟩ := (mem_SE hX).mp hm
    rw [hX.record_eq hr hr' (hid.trans hid'.symm)]
    exact hf')
  have hle : ∀ y ∈ SE L X c, y.2 ≤ t := by
    intro y hy
    by_contra hgt
    have hgM := R.guardM 0 y hy (t + 1) (by omega)
    obtain ⟨hx, -⟩ := R.observes_full hacyc (MbarRing.Round.Slot.present_of_guard hgM) 0
    have hgP := R.guardP _ (0, t + 1) hx (t + 1) (by omega) le_rfl
    exact hnot (R.observes_empty hacyc (a := 0) (n := t)
      (MbarRing.Round.Slot.present_of_guard hgP) b).1
  have hunits : unitsBefore (X.objects ((slot L c).empty 0)) i < 10 * (t + 1) := by
    have hU := MbarRing.Round.units_le_of_uses hch
      (fun y : Fin 10 × Nat => Ref.thread (ackEv L X c y.1 y.2)) (SE L X c) (i := i)
      (fun k q c' tx' hk hqf hqa => (ack_count hpre hX ht k q c' tx' hk hqf hqa).1)
      (fun k _ q c' tx' hk hqf hqa => (ack_count hpre hX ht k q c' tx' hk hqf hqa).2)
    have hC := MbarRing.Round.card_lt_of_uses (SE L X c) (Q := t + 1)
      (fun y hy => by have := hle y hy; omega) (z := (b, t)) (by simp) hnot
    simp only [Fintype.card_fin] at hC
    omega
  have hpolls : ∀ q, 1 ≤ q → q ≤ t → ∃ k w sk, k < i ∧
      (X.objects ((slot L c).empty 0))[k]? = some w ∧ w.reply.waited = some true ∧
      stateBefore (X.objects ((slot L c).empty 0)) k = some sk ∧ sk.phase = q := by
    intro q h1 hq
    obtain ⟨hpres, hpath⟩ := R.reach_consumer_op hacyc 0 (b := b) (t := t)
      (op := ackEv L X c b t) (fun j hj => ack_guard hpre hX ht he hj) h1 hq
    obtain ⟨k, w, sk, hk, hwid, hww, hsk, hph, -⟩ := epoll_phase hpre hX ht h1 hpres
    refine ⟨k, w, sk, ?_, hk, hww, hsk, hph⟩
    rcases Nat.lt_trichotomy k i with h | rfl | h
    · exact h
    · rw [hi] at hk
      cases hk
      obtain ⟨-, p, -, hpa, -⟩ := hch.okPoll hi hww
      rw [ha1] at hpa
      cases hpa
    · exact absurd ⟨i, k, r, w, hi, hid, hk, hwid, h⟩
        (MbarRing.Round.Slot.not_before_of_reach hX hpath)
  obtain ⟨h1, h2⟩ := hch.arrive_fault_free hni (s := t) hi ha1 (fun st' hst' => by
    rw [ring_expected (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hst']
    simp only [Bar.count]
    omega) hpolls
  exact hf (RecordOk.arrive_fault hok ha1 (by decide) (by decide)
    (by simp only [validTx, limit]; omega) h1 h2)

end ClcRing

/-- **The CLC response ring's facts**: every record of a cluster's response and
acknowledgement barriers is fault-free. -/
theorem clcFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ClcFacts L X where
  fault_free := by
    intro c m hm r hr
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    rcases (ClcRing.slot L c).objects_cases hm with ⟨f, rfl⟩ | ⟨a, rfl⟩
    · cases ha : r.action with
      | init n => exact ClcRing.init_ok (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hr ha
      | pollParity p ok =>
        exact ClcRing.poll_clean (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos r hr ⟨p, ok, ha⟩
      | arrive n tx => exact ClcRing.resp_arrive_ok hpre hX ht hi ha
      | completeTx n => exact ClcRing.resp_complete_ok hpre hX ht hi ha
      | inval => exact (objects_noInval hX ht _ r hr ha).elim
      | increment => exact (no_increment hX ht hr ha).elim
    · obtain rfl : a = 0 := Subsingleton.elim _ _
      cases ha : r.action with
      | init n => exact ClcRing.init_ok (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hr ha
      | inval => exact (objects_noInval hX ht _ r hr ha).elim
      | increment => exact (no_increment hX ht hr ha).elim
      | pollParity p ok =>
        exact ClcRing.poll_clean (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos r hr ⟨p, ok, ha⟩
      | arrive n tx => exact ClcRing.ack_ok hpre hX ht hi ha
      | completeTx n =>
        cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos hr with
        | arrive _ _ ha' => rw [ha] at ha'; cases ha'
        | init ha' => rw [ha] at ha'; cases ha'
        | poll _ _ ha' => rw [ha] at ha'; cases ha'
        | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
        | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
        | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby

namespace ClcRing

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
