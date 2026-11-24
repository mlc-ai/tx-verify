-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Lemmas.Flow.NthEv
public import Lemmas.Protocol.MbarCount
public import Lemmas.Protocol.PollIndex
public import Lemmas.Protocol.MbarRingItems
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Slot
public import Lemmas.Protocol.Poller

@[expose] public section

/-! # The records of the accumulator ring

The records of buffer `j`'s barriers, from the thread facts. Every record of a buffer's barrier
is its CTA thread 0's initialization, a poll, or a unit arrival without bytes
(`acc_record_cases`); the initialization is the first record and does not fault, so a poll
never faults (`poll_clean`), every state has the barrier's count (`expected_eq`) and a zero
transaction counter (`tx_zero_acc`). An arrival on a full barrier is the notification of a
commit of the buffer's producer, the polling lane of MMA warp `8 + j` of the leader CTA
(`notify_record`); its polls of the empty barrier guard the commit (`commit_guard`). An
arrival on the empty barrier is a consumer thread's (`empty_arrival`); its polls of its full
barrier guard the arrival (`arrive_guard`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An arrival without bytes. -/
def isArrival (q : Record Ref) : Bool := decide (q.action = .arrive 1 0 ∧ q.fault = none)

/-- A commit notification, faulting or not. -/
def isNotify (q : Record Ref) : Bool := decide (q.action = .arrive 1 0)

theorem isArrival_iff (q : Record Ref) :
    isArrival q = true ↔ q.action = .arrive 1 0 ∧ q.fault = none := by
  simp [isArrival]

/-- The producer of buffer `j`: the thread of MMA warp `8 + j` of the leader CTA that polls the
empty barrier successfully. -/
def producer (L : Launch) (X : Execution) (c : Nat) (j : Fin 2) : Nat :=
  pollerOf X (producerThread L c j) ((slot L c j).empty 0) (2 * c * L.block + 32 * (8 + j.val))

theorem producer_thread (hpre : Pre P L mem0) (c : Nat) (j : Fin 2) :
    producerThread L c j (producer L X c j) = true := by
  have := j.isLt
  refine pollerOf_sel ?_
  simp only [producerThread, decide_eq_true_eq, hpre.block]
  omega

theorem producer_cta (hpre : Pre P L mem0) (c : Nat) (j : Fin 2) :
    producer L X c j / L.block = 2 * c := by
  have h := producer_thread (X := X) hpre c j
  simp only [producerThread, decide_eq_true_eq] at h
  exact h.1

/-- A thread of the producer selector that polls the empty barrier successfully is
`producer`. -/
theorem producer_eq (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {j : Fin 2} {g jj pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hg : producerThread L c j g = true)
    (he : X.get (g, jj) = some ⟨pc, .wait ((slot L c j).empty 0) p true acq sc⟩) :
    g = producer L X c j := by
  refine pollerOf_eq (fun hg hh he he' => ?_) hg he
  simp only [producerThread, decide_eq_true_eq] at hg hh
  have := j.isLt
  exact mma_unique hX ht (hg.1.trans hh.1.symm) (hg.2.trans hh.2.symm) (by omega) he he' rfl rfl

/-- The source of a record of buffer `j`'s full barrier `k`. -/
theorem full_src (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {j k : Fin 2} {r : Record Ref} (hr : r ∈ X.objects ((slot L c j).full k)) :
    BarSource L X ⟨.acc, j.val, true⟩ (2 * c + k.val) r :=
  bar_source (b := ⟨.acc, j.val, true⟩) hX ht j.isLt hr

/-- The source of a record of buffer `j`'s empty barrier. -/
theorem empty_src (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {j : Fin 2} {a : Fin 1} {r : Record Ref} (hr : r ∈ X.objects ((slot L c j).empty a)) :
    BarSource L X ⟨.acc, j.val, false⟩ (2 * c) r :=
  bar_source (b := ⟨.acc, j.val, false⟩) hX ht j.isLt hr

/-- A commit notifying a full barrier is the producer's, on its CTA's full barrier. -/
theorem notify_producer (ht : ThreadFacts L X) {c g jj : Nat} {j : Fin 2} {mm : Mma.D}
    (hg : g < L.threads) (hle : jj ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g jj = some (some (.inr (.mma mm)))) (hjw : j.val = mm.w % 2)
    (hc : g / L.block = 2 * c) : producerThread L c j g = true := by
  have hw := ht.role_warp hg hle hσ
  simp only [roleWarp] at hw
  simp only [producerThread, decide_eq_true_eq]
  omega

/-- An object action of a commit notification is of a notified commit to its target. -/
theorem notify_facts {m : Loc} {c : EvId} {rank : Fin 16} {act : MBarrier.Action}
    (h : objectAction X X.async m (.async c (.tcNotify rank)) = some act) :
    ∃ pc s, X.get c = some ⟨pc, .tc (.commit s)⟩ ∧ TcCommit.target s rank = some m ∧
      rank ∈ X.tcNotified c := by
  simp only [objectAction] at h
  cases hg : X.get c with
  | none => simp [hg] at h
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    cases k with
    | tc k' =>
      cases k' with
      | commit s =>
        by_cases hc : TcCommit.target s rank = some m ∧ rank ∈ X.tcNotified c
        · exact ⟨pc, s, rfl, hc.1, hc.2⟩
        · simp [hg, hc] at h
      | _ => simp [hg] at h
    | _ => simp [hg] at h

/-! ### The records of a buffer's barriers -/

/-- Every record of an accumulator barrier is an initialization, a poll, or a unit arrival
without bytes. -/
theorem acc_record_cases (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {j : Fin 2} {f : Bool} {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩)) :
    (∃ n, r.action = .init n) ∨ (∃ p ok, r.action = .pollParity p ok) ∨
      r.action = .arrive 1 0 := by
  cases bar_source (b := ⟨.acc, j.val, f⟩) hX ht j.isLt hr with
  | init ha => exact .inl ⟨_, ha⟩
  | poll _ _ ha => exact .inr (.inl ⟨_, _, ha⟩)
  | arrive _ _ ha => exact .inr (.inr (by cases f <;> exact ha))
  | notify _ _ _ ha => exact .inr (.inr ha)
  | copy _ _ _ _ _ hby => cases f <;> simp [Bar.copyBy] at hby
  | clc _ _ _ _ _ hby => cases f <;> simp [Bar.clcBy] at hby

/-- The first record of an accumulator barrier is its successful initialization, and every
other record has a state before it. -/
theorem acc_init (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {j : Fin 2} {f : Bool} {cta i : Nat} {r : Record Ref}
    (hi : (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩))[i]? = some r) :
    (∃ n, r.action = .init n) ∧ i = 0 ∧ r.fault = none ∨
      (∃ s, stateBefore (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩)) i = some s) := by
  have hr := List.mem_of_getElem? hi
  have hch := X.objects_checked hX (Bar.loc L cta ⟨.acc, j.val, f⟩)
  have hni := objects_noInval hX ht (Bar.loc L cta ⟨.acc, j.val, f⟩)
  obtain ⟨r0, h0, hid0, ha0, hf0⟩ := first_record hpre hX ht (b := ⟨.acc, j.val, f⟩) j.isLt hr
  obtain ⟨hfirst, hstate⟩ := ObjectInit.first_or_initialized hch hni hi h0 ha0 hf0
  by_cases hid : r.id = r0.id
  · have := hfirst hid
    subst this
    rw [h0] at hi
    cases hi
    exact .inl ⟨⟨_, ha0⟩, rfl, hf0⟩
  · exact .inr (hstate hid)

/-- A poll of an accumulator barrier does not fault. -/
theorem poll_clean (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {j : Fin 2} {f : Bool} {cta : Nat} :
    ∀ q ∈ X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩),
      (∃ p ok, q.action = .pollParity p ok) → q.fault = none := by
  intro q hq ⟨p, ok, ha⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  rcases acc_init hpre hX ht hi with ⟨⟨n, hn⟩, -, -⟩ | ⟨s, hs⟩
  · rw [hn] at ha; cases ha
  · exact poll_fault_none (X.objects_checked hX _) hi hs ha

/-- Every state of an accumulator barrier has the barrier's count. -/
theorem expected_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {j : Fin 2} {f : Bool} {cta : Nat} :
    ∀ k st, stateBefore (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩)) k = some st →
      st.expected = Bar.count ⟨.acc, j.val, f⟩ := by
  intro k st hs
  have hch := X.objects_checked hX (Bar.loc L cta ⟨.acc, j.val, f⟩)
  have hni := objects_noInval hX ht (Bar.loc L cta ⟨.acc, j.val, f⟩)
  unfold stateBefore at hs
  split_ifs at hs with hk0
  obtain ⟨r, hr, -⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨r0, h0, -, ha0, hf0⟩ := first_record hpre hX ht (b := ⟨.acc, j.val, f⟩) j.isLt
    (List.mem_of_getElem? hr)
  have hlt := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨s, hs', he⟩ := ObjectInit.checked_expected_after_init hch hni h0 ha0 hf0
    (show 0 < k by omega) (by omega)
  unfold stateBefore at hs'
  simp only [hk0, ↓reduceIte, hs] at hs'
  cases hs'
  exact he

/-- Every state of an accumulator barrier has a zero transaction counter. -/
theorem tx_zero_acc (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {j : Fin 2}
    {f : Bool} {cta k : Nat} {st : State}
    (hs : stateBefore (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩)) k = some st) : st.tx = 0 :=
  tx_zero (X.objects_checked hX _) (objects_noInval hX ht _)
    (fun r hr n b ha => by
      rcases acc_record_cases hX ht hr with ⟨_, h⟩ | ⟨_, _, h⟩ | h <;> rw [h] at ha <;> cases ha
      rfl)
    (fun r hr n ha => by
      rcases acc_record_cases hX ht hr with ⟨_, h⟩ | ⟨_, _, h⟩ | h <;> rw [h] at ha <;> cases ha)
    hs

/-- A record of an accumulator barrier does not fault when its arrivals neither underflow nor
arrive in an unobserved phase. -/
theorem acc_fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {j : Fin 2} {f : Bool} {cta i : Nat} {r : Record Ref}
    (hi : (X.objects (Bar.loc L cta ⟨.acc, j.val, f⟩))[i]? = some r)
    (harr : r.action = .arrive 1 0 →
      r.fault ≠ some .arrivalUnderflow ∧ r.fault ≠ some .precedingPhaseNotObserved) :
    r.fault = none := by
  have hr := List.mem_of_getElem? hi
  rcases acc_init hpre hX ht hi with ⟨-, -, hf⟩ | ⟨s, hs⟩
  · exact hf
  rcases acc_record_cases hX ht hr with ⟨n, ha⟩ | ⟨p, ok, ha⟩ | ha
  · -- a second initialization is the first one
    obtain ⟨hid, -⟩ := init_source hX ht (b := ⟨.acc, j.val, f⟩) j.isLt hr ha
    obtain ⟨r0, h0, hid0, -, hf0⟩ := first_record hpre hX ht (b := ⟨.acc, j.val, f⟩) j.isLt hr
    have := ObjectInit.checked_record_index_eq (X.objects_checked hX _) hi h0 (hid.trans hid0.symm)
    subst this
    rw [h0] at hi
    cases hi
    exact hf0
  · exact poll_fault_none (X.objects_checked hX _) hi hs ha
  · exact arrive_fault_none (X.objects_checked hX _) hi hs (tx_zero_acc hX ht hs) ha
      (harr ha).1 (harr ha).2

/-! ### Notifications and arrivals -/

/-- **A notification is of the producer's commit.** An arrival on buffer `j`'s full barrier `k`
is the notification of rank `k` of a commit of the buffer's producer to the leader CTA's full
barrier. -/
theorem notify_record (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {x : Record Ref}
    (hx : x ∈ X.objects ((slot L c j).full k)) (hda : x.action = .arrive 1 0) :
    ∃ jc pc sp, x.id = .async (producer L X c j, jc) (.tcNotify ⟨k.val, by omega⟩) ∧
      X.get (producer L X c j, jc) = some ⟨pc, .tc (.commit sp)⟩ ∧
      sp.mbar = (slot L c j).full 0 ∧
      TcCommit.target sp ⟨k.val, by omega⟩ = some ((slot L c j).full k) ∧
      (⟨k.val, by omega⟩ : Fin 16) ∈ X.tcNotified (producer L X c j, jc) := by
  have hblock := hpre.block
  cases full_src hX ht hx with
  | init ha' => rw [hda] at ha'; cases ha'
  | poll _ _ ha' => rw [hda] at ha'; cases ha'
  | arrive _ _ _ _ hby => exact absurd hby (by simp [Bar.arriveBy])
  | copy _ _ _ _ _ hby => exact absurd hby (by simp [Bar.copyBy])
  | clc _ _ _ _ _ hby => exact absurd hby (by simp [Bar.clcBy])
  | @notify h kk pc sp rank dd hid he htg ha' hσ hby hlead hrank hcta hmb =>
    obtain ⟨mm, rfl, hjw⟩ := hby
    have hh := Frame.lt_of_get hX he
    have hk := k.isLt
    have hprod := notify_producer (c := c) ht hh (idx_le he) hσ hjw (by omega)
    have hcb := ht.commit_budget (b := ⟨.acc, j.val, true⟩) hh he hσ rfl htg j.isLt
    have hlc : h / L.block = 2 * c := by
      simp only [producerThread, decide_eq_true_eq] at hprod; exact hprod.1
    rw [hlc] at hcb hmb
    obtain ⟨j', pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := h) (k := kk)
      (m := (slot L c j).empty 0) (by exact Nat.lt_of_lt_of_le (Nat.succ_pos _) hcb)
    have hp := producer_eq hX ht hprod he'
    have hr : rank = ⟨k.val, by omega⟩ := Fin.ext (by simp only; omega)
    rw [hr] at hid htg
    have hact := ((hX.tma.2.2.1 _).2.1 x hx).1
    rw [hid] at hact
    obtain ⟨-, -, -, -, hnot⟩ := notify_facts hact
    subst hp
    exact ⟨kk, pc, sp, hid, he, hmb, htg, hnot⟩

/-- The producer's spinning empty polls resume its commits: a commit of the producer to its
buffer's full barrier, with `s` earlier ones, is guarded by its successful empty polls with
`n` earlier ones for `n ≤ s`. -/
theorem commit_guard (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {kk pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (producer L X c j, kk) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp ⟨k.val, by omega⟩ = some ((slot L c j).full k)) {n : Nat}
    (hn : n ≤ ((X.tr (producer L X c j)).take kk).countP (commitsTo ((slot L c j).full 0))) :
    Resumes kernel X
      (producer L X c j, MbarRing.Poll.nth X ((slot L c j).empty 0) (producer L X c j) n)
      (producer L X c j, kk) := by
  have hh := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  have hcb := ht.commit_budget (b := ⟨.acc, j.val, true⟩) (cta := 2 * c + k.val) hh he hσ rfl
    htg j.isLt
  have hmb : sp.mbar = (slot L c j).full 0 := by
    obtain ⟨-, -, -, -, hmb⟩ := (ht.ring_event hh he hσ).commit _ _ _ _ rfl htg j.isLt
    rw [hmb, producer_cta hpre]
    rfl
  rw [hmb, producer_cta hpre] at hcb
  have hcb' : ((X.tr (producer L X c j)).take kk).countP (commitsTo ((slot L c j).full 0)) + 1 ≤
      okPolls ((slot L c j).empty 0) ((X.tr (producer L X c j)).take kk) := hcb
  exact MbarRing.Poll.guard (fun w pc m q acq sc hw => ht.wait_spins (Frame.lt_of_get hX hw) hw)
    (len_of_get he) (by omega)

/-- An arrival on buffer `j`'s empty barrier is a consumer thread's arrival. -/
theorem empty_arrival (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {x : Record Ref}
    (hx : x ∈ X.objects ((slot L c j).empty 0)) (ha : x.action = .arrive 1 0) :
    ∃ b ka pc rel sc, x.id = .thread (consumerOf L c j b, ka) ∧
      X.get (consumerOf L c j b, ka) = some ⟨pc, .arrive ((slot L c j).empty 0) 0 1 rel sc⟩ := by
  have hblock := hpre.block
  cases empty_src hX ht hx with
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ _ _ hby => exact absurd hby (by simp [Bar.copyBy])
  | clc _ _ _ _ _ hby => exact absurd hby (by simp [Bar.clcBy])
  | notify _ _ _ _ _ hby => exact absurd hby (by simp [Bar.commitBy])
  | @arrive g jj pc rel sc d hid he ha' hσ hby hcta =>
    obtain ⟨⟨cs, rfl⟩, hjw⟩ := hby
    simp only [Bar.arriveCta, Bar.arriveLeader, ↓reduceIte] at hcta
    have hg := Frame.lt_of_get hX he
    have hw := ht.role_warp hg (idx_le he) hσ
    simp only [roleWarp] at hw
    have hj := j.isLt
    have hc' : g / L.block / 2 = c := by omega
    have hgb := consumerOf_of (L := L) (j := j) hc' hjw.symm
    refine ⟨_, jj, pc, rel, sc, by rw [hgb]; exact hid, by rw [hgb]; exact he⟩

/-- A consumer's spinning full polls guard its arrivals: an arrival of consumer `b` on the
empty barrier, with `t` earlier ones, is guarded by its successful full polls with `j' ≤ t`
earlier ones. -/
theorem arrive_guard (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {ka pc tx cnt : Nat} {rel : Bool}
    {sc : MbarScope}
    (he : X.get (consumerOf L c j b, ka) =
      some ⟨pc, .arrive ((slot L c j).empty 0) tx cnt rel sc⟩) {n : Nat}
    (hn : n ≤ arrivals ((slot L c j).empty 0) ((X.tr (consumerOf L c j b)).take ka)) :
    Resumes kernel X
      (consumerOf L c j b, MbarRing.Poll.nth X ((slot L c j).full ((slot L c j).owner b))
        (consumerOf L c j b) n) (consumerOf L c j b, ka) := by
  have hblock := hpre.block
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  have hab := ht.arrival_budget (b := ⟨.acc, j.val, false⟩) (cta := 2 * c) hg he hσ rfl j.isLt
  have hgate : (Bar.gate ⟨.acc, j.val, false⟩).loc L (consumerOf L c j b / L.block) =
      (slot L c j).full ((slot L c j).owner b) := by
    rw [consumerOf_div (by omega)]
    rfl
  rw [hgate] at hab
  have hab' : arrivals ((slot L c j).empty 0) ((X.tr (consumerOf L c j b)).take ka) + 1 ≤
      okPolls ((slot L c j).full ((slot L c j).owner b)) ((X.tr (consumerOf L c j b)).take ka) :=
    hab
  exact MbarRing.Poll.guard (fun w pc m q acq sc hw => ht.wait_spins (Frame.lt_of_get hX hw) hw)
    (len_of_get he) (by omega)

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
