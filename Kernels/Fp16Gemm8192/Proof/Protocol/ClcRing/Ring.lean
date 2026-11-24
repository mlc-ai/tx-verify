-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Select
public import Lemmas.Flow.NthEv
public import Lemmas.Protocol.MbarUnitTx
public import Lemmas.Protocol.MbarRingItems
public import Lemmas.Protocol.PollIndex

@[expose] public section

/-! # The CLC response ring as a ring of items

Cluster `c`'s response ring is an instance of `MbarRing.Items.Ring` (`ring`) with one producer,
the leader scheduler, ten consumers and two full objects, the response barriers of the
cluster's two CTAs. The item of response barrier `f` for use `s` is the completion of the
leader's request numbered `s`, multicast to both CTAs: the request is guarded by the leader's
successful acknowledgement polls `1, …, s` (`clc_budget`), and its issue reaches its
completion by the stages of the request (`clc_reach`). Consumer `b`'s acknowledgement of use
`t` is its arrival numbered `t` on the acknowledgement barrier, guarded by its successful
response polls `0, …, t` (`arrival_budget`). The schedulers' arrivals expecting the response
are not items.

Each object is read through its own history: a successful poll observes every counted item of
the phase it observes (`Consistent.observed_of_phase`); an observed response phase holds a
completion (`UnitTx.completion_in_phase`), an observed acknowledgement phase ten
acknowledgements (`card_unit_arrivals_phase`); a thread's later polls observe later phases
(`Poll.observed_lt`, from its poll parity). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The objects' histories -/

theorem stateBefore_lt {log : List (Record Ref)} {k : Nat} {st : State}
    (hs : stateBefore log k = some st) : 1 ≤ k ∧ k ≤ log.length := by
  unfold stateBefore at hs
  split_ifs at hs with h0
  obtain ⟨r, hr, -⟩ := Option.bind_eq_some_iff.mp hs
  have := (List.getElem?_eq_some_iff.mp hr).1
  omega

/-- After its first record, a ring barrier's history has a state, with the barrier's count. -/
theorem ring_state (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} (hb : b.Valid) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (b.loc L cta)) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ (X.objects (b.loc L cta)).length) :
    ∃ s, stateBefore (X.objects (b.loc L cta)) j = some s ∧ s.expected = b.count := by
  obtain ⟨r0, h0, -, ha, hf⟩ := first_record hpre hX ht hb hr
  exact ObjectInit.checked_expected_after_init (hX.tma.2.2.1 _).1 (objects_noInval hX ht _) h0 ha hf
      (by omega) hj

/-- Every state of a ring barrier expects the barrier's count. -/
theorem ring_expected (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} (hb : b.Valid) {cta k : Nat} {st : State}
    (hs : stateBefore (X.objects (b.loc L cta)) k = some st) : st.expected = b.count := by
  obtain ⟨hk1, hkl⟩ := stateBefore_lt hs
  obtain ⟨r, hr⟩ : ∃ r, (X.objects (b.loc L cta))[0]? = some r :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨s, hs', he⟩ := ring_state hpre hX ht hb (List.mem_of_getElem? hr) hk1 hkl
  rw [hs] at hs'
  cases hs'
  exact he

/-- A record of a ring barrier after its first has a state before it. -/
theorem ring_state_at (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} (hb : b.Valid) {cta i : Nat} {r : Record Ref}
    (hi : (X.objects (b.loc L cta))[i]? = some r) (hpos : 0 < i) :
    ∃ s, stateBefore (X.objects (b.loc L cta)) i = some s := by
  have hl := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨s, hs, -⟩ := ring_state hpre hX ht hb (List.mem_of_getElem? hi) hpos (by omega)
  exact ⟨s, hs⟩

/-- A record of a ring barrier other than its initialization is after the first. -/
theorem ring_pos (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} (hb : b.Valid) {cta i : Nat} {r : Record Ref}
    (hi : (X.objects (b.loc L cta))[i]? = some r) (hni : ∀ n, r.action ≠ .init n) : 0 < i := by
  obtain ⟨r0, h0, -, ha, -⟩ := first_record hpre hX ht hb (List.mem_of_getElem? hi)
  rcases Nat.eq_zero_or_pos i with rfl | h
  · rw [h0] at hi
    cases hi
    exact absurd ha (hni _)
  · exact h

/-- The polls of a ring barrier do not fault: they follow its initialization. -/
theorem poll_clean (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} (hb : b.Valid) {cta : Nat} :
    ∀ q ∈ X.objects (b.loc L cta), (∃ p ok, q.action = .pollParity p ok) → q.fault = none := by
  rintro q hq ⟨p, ok, ha⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  obtain ⟨s, hs⟩ := ring_state_at hpre hX ht hb hi
    (ring_pos hpre hX ht hb hi (by rw [ha]; intro n h; cases h))
  have hok := (hX.tma.2.2.1 _).1.at hi
  rw [hs] at hok
  unfold RecordOk at hok
  rw [ha] at hok
  simp only [perform, pure, Except.pure] at hok
  exact hok.2

/-- A thread's successful polls of a response barrier alternate parity. -/
theorem resp_alt (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (g C : Nat) :
    SelectedAlternates (objectThreadSelected g) (X.objects (Bar.loc L C ⟨.clc, 0, true⟩)) 0 :=
  MbarRing.Poll.alternates hX (poll_clean (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos)
    fun k pc p acq sc he => by
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    have := ht.poll_parity (b := ⟨.clc, 0, true⟩) hg he hσ rfl Nat.one_pos
    simpa [Bar.pollOffset] using this

/-- A thread's successful polls of an acknowledgement barrier alternate parity, after a first
free one. -/
theorem ack_alt (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (g C : Nat) :
    SelectedAlternates (objectThreadSelected g) (X.objects (Bar.loc L C ⟨.clc, 0, false⟩)) 1 :=
  MbarRing.Poll.alternates hX (poll_clean (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos)
    fun k pc p acq sc he => by
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    have := ht.poll_parity (b := ⟨.clc, 0, false⟩) hg he hσ rfl Nat.one_pos
    simpa [Bar.pollOffset] using this

/-- A response barrier's history: count one, arrivals expecting 16 bytes, completions of 16. -/
theorem resp_unitTx (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (C : Nat) : UnitTx (X.objects (Bar.loc L C ⟨.clc, 0, true⟩)) 16 where
  arrive r hr _ c tx ha := by
    cases bar_source (b := ⟨.clc, 0, true⟩) hX ht Nat.one_pos hr with
    | arrive _ _ ha' => rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl⟩
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
    | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
    | clc _ _ _ ha' => rw [ha] at ha'; cases ha'
  complete r hr _ n ha := by
    cases bar_source (b := ⟨.clc, 0, true⟩) hX ht Nat.one_pos hr with
    | clc _ _ _ ha' => rw [ha] at ha'; cases ha'; rfl
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | arrive _ _ ha' => rw [ha] at ha'; cases ha'
    | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
    | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
  expected k st hs := ring_expected (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hs

/-! ### The threads and their operations by use -/

/-- Consumer `b`'s thread in cluster `c`: the thread of its selector that polls its response
barrier successfully (lane 0 of the selector's warp when none does). -/
def thr (L : Launch) (X : Execution) (c : Nat) (b : Fin 10) : Nat :=
  pollerOf X (consumerSel L c b) ((slot L c).full ((slot L c).owner b))
    ((2 * c + ctaOf b) * L.block + 32 * warpOf b)

theorem warpOf_lt : ∀ b : Fin 10, warpOf b < 12 := by decide

theorem thr_sel (hpre : Pre P L mem0) (c : Nat) (b : Fin 10) :
    consumerSel L c b (thr L X c b) = true := by
  have hblock := hpre.block
  have hw := warpOf_lt b
  refine pollerOf_sel ?_
  simp only [consumerSel, decide_eq_true_eq, hblock]
  omega

/-- A thread of consumer `b`'s selector that polls its response barrier successfully is its
thread. -/
theorem thr_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g j pc p : Nat} {acq : Bool}
    {sc : MbarScope} (hg : consumerSel L c b g = true)
    (he : X.get (g, j) = some ⟨pc, .wait ((slot L c).full ((slot L c).owner b)) p true acq sc⟩) :
    g = thr L X c b :=
  pollerOf_eq (fun hg' hh he' hf' => (sel_eq hpre hX ht hg' hh he' hf' (poll_state ht hX he')
    trivial trivial (poll_state ht hX hf')).symm) hg he

theorem sel_cta {c : Nat} {b : Fin 10} {g : Nat} (hg : consumerSel L c b g = true) :
    g / L.block = 2 * c + ctaOf b := by
  simp only [consumerSel, decide_eq_true_eq] at hg
  exact hg.1

/-- An acknowledgement of consumer `b` is by its thread, which polled its response barrier
first. -/
theorem ack_thr (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {g k pc tx n : Nat} {rel : Bool}
    {sc : MbarScope} (hg : consumerSel L c b g = true)
    (he : X.get (g, k) = some ⟨pc, .arrive ((slot L c).empty 0) tx n rel sc⟩) :
    g = thr L X c b ∧ arrivals ((slot L c).empty 0) ((X.tr g).take k) + 1 ≤
      okPolls ((slot L c).full ((slot L c).owner b)) ((X.tr g).take k) := by
  have hgt := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  have hab := ht.arrival_budget (b := ⟨.clc, 0, false⟩) (cta := 2 * c) hgt he hσ rfl Nat.one_pos
  have hloc : (Bar.gate ⟨.clc, 0, false⟩).loc L (g / L.block) =
      (slot L c).full ((slot L c).owner b) := by
    rw [sel_cta hg]
    rfl
  rw [hloc] at hab
  simp only [Bar.gateSlack] at hab
  obtain ⟨j, pc', p', acq', sc', -, he'⟩ := exists_okPoll (X := X) (g := g) (k := k)
    (m := (slot L c).full ((slot L c).owner b)) (by omega)
  exact ⟨thr_eq hpre hX ht hg he', hab⟩

/-- The leader's requests of cluster `c`. -/
abbrev reqP (L : Launch) (c : Nat) : Event → Bool := clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)

/-- The acknowledgements of cluster `c`. -/
abbrev ackP (L : Launch) (c : Nat) : Event → Bool := arrivesOn ((slot L c).empty 0)

/-- The position of the leader's request numbered `s`. -/
def reqIdx (L : Launch) (X : Execution) (c s : Nat) : Nat := nthEv X (reqP L c) (producer L X c) s

/-- The position of consumer `b`'s acknowledgement numbered `t`. -/
def ackIdx (L : Launch) (X : Execution) (c : Nat) (b : Fin 10) (t : Nat) : Nat :=
  nthEv X (ackP L c) (thr L X c b) t

/-- Consumer `b`'s acknowledgement numbered `t`. -/
abbrev ackEv (L : Launch) (X : Execution) (c : Nat) (b : Fin 10) (t : Nat) : EvId :=
  (thr L X c b, ackIdx L X c b t)

/-- The completion of the request numbered `s` on response barrier `f`. -/
abbrev item (L : Launch) (X : Execution) (c : Nat) (f : Fin 2) (s : Nat) : Ref :=
  .async (producer L X c, reqIdx L X c s) (.notify (.cta (2 * c + f.val)))

/-- Consumer `b`'s successful response poll with `j` earlier ones. -/
abbrev fpoll (L : Launch) (X : Execution) (c : Nat) (b : Fin 10) (j : Nat) : EvId :=
  (thr L X c b, MbarRing.Poll.nth X ((slot L c).full ((slot L c).owner b)) (thr L X c b) j)

/-- The leader's successful acknowledgement poll with `n` earlier ones. -/
abbrev epoll (L : Launch) (X : Execution) (c n : Nat) : EvId :=
  (producer L X c, MbarRing.Poll.nth X ((slot L c).empty 0) (producer L X c) n)

open Classical in
/-- The counted completions of response barrier `f`: its fault-free records of requests. -/
def SF (L : Launch) (X : Execution) (c : Nat) (f : Fin 2) : Finset (Fin 1 × Nat) :=
  (Finset.univ ×ˢ Finset.range ((X.tr (producer L X c)).length + 1)).filter fun x =>
    ∃ r ∈ X.objects ((slot L c).full f), r.id = item L X c f x.2 ∧ r.fault = none

open Classical in
/-- The counted acknowledgements: the acknowledgement barrier's fault-free records of them. -/
def SE (L : Launch) (X : Execution) (c : Nat) : Finset (Fin 10 × Nat) :=
  (Finset.univ ×ˢ Finset.range ((∑ b : Fin 10, (X.tr (thr L X c b)).length) + 1)).filter fun y =>
    ∃ r ∈ X.objects ((slot L c).empty 0), r.id = .thread (ackEv L X c y.1 y.2) ∧ r.fault = none

/-- The request with `s` earlier ones, when it exists. -/
theorem req_spec {c s : Nat} {e : Event} (he : X.get (producer L X c, reqIdx L X c s) = some e) :
    reqP L c e = true ∧
      ((X.tr (producer L X c)).take (reqIdx L X c s)).countP (reqP L c) = s := by
  have hlt := nthEv_lt_iff.mp (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨e', he', hp, hc⟩ := nthEv_spec hlt
  unfold reqIdx at he
  rw [he] at he'
  cases he'
  exact ⟨hp, hc⟩

/-- The acknowledgement with `t` earlier ones, when it exists. -/
theorem ack_spec {c : Nat} {b : Fin 10} {t : Nat} {e : Event}
    (he : X.get (ackEv L X c b t) = some e) :
    ackP L c e = true ∧ ((X.tr (thr L X c b)).take (ackIdx L X c b t)).countP (ackP L c) = t := by
  have hlt := nthEv_lt_iff.mp (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨e', he', hp, hc⟩ := nthEv_spec hlt
  have he2 : X.get (thr L X c b, nthEv X (ackP L c) (thr L X c b) t) = some e := he
  rw [he2] at he'
  cases he'
  exact ⟨hp, hc⟩

theorem mem_SF (hX : Consistent L kernel Prod mem0 X) {c : Nat} {f : Fin 2} {x : Fin 1 × Nat} :
    x ∈ SF L X c f ↔ ∃ r ∈ X.objects ((slot L c).full f), r.id = item L X c f x.2 ∧
      r.fault = none := by
  classical
  unfold SF
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨r, hr, hid, -⟩ := h
  rw [Finset.mem_product]
  refine ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩
  obtain ⟨sp, tg, hci, -⟩ := hX.clc_notified hr hid
  obtain ⟨pc, he⟩ := hci
  have hlt := nthEv_lt_iff.mp (List.getElem?_eq_some_iff.mp he).1
  have := List.countP_le_length (p := reqP L c) (l := X.tr (producer L X c))
  omega

theorem mem_SE (hX : Consistent L kernel Prod mem0 X) {c : Nat} {y : Fin 10 × Nat} :
    y ∈ SE L X c ↔ ∃ r ∈ X.objects ((slot L c).empty 0), r.id = .thread (ackEv L X c y.1 y.2) ∧
      r.fault = none := by
  classical
  unfold SE
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨r, hr, hid, -⟩ := h
  rw [Finset.mem_product]
  refine ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩
  obtain ⟨ev, he⟩ : X.RefPresent (.thread (ackEv L X c y.1 y.2)) :=
    hid ▸ object_record_present hX.tma hr
  have hlt := nthEv_lt_iff.mp (List.getElem?_eq_some_iff.mp he).1
  have h1 := List.countP_le_length (p := ackP L c) (l := X.tr (thr L X c y.1))
  have h2 : (X.tr (thr L X c y.1)).length ≤ ∑ b : Fin 10, (X.tr (thr L X c b)).length :=
    Finset.single_le_sum (f := fun b : Fin 10 => (X.tr (thr L X c b)).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ y.1)
  omega

/-! ### Thread layer: guards and stages -/

/-- A request's issue reaches its notification of a CTA through the request's stages. -/
theorem clc_reach (hX : Consistent L kernel Prod mem0 X) {i : EvId} {s : Clc.Spec}
    {targets : List Nat} (hi : X.ClcIssue i s targets) {c : Nat} (hn : c ∈ (X.clc i).notified) :
    Relation.ReflTransGen (DepStep L kernel X) (.thread i, false)
      (.async i (.notify (.cta c)), false) := by
  have hw := (hX.clc.2.2.2.1 i s targets hi).1.notified c hn
  have hr := ((hX.clc.2.2.2.1 i s targets hi).1.writes c hw).2
  have hp0 : X.AsyncPresent i .resolve := hr
  have hp1 : X.AsyncPresent i (.write (.cta c)) := hw
  have hp2 : X.AsyncPresent i (.notify (.cta c)) := hn
  obtain ⟨pc, hpc⟩ := hi
  exact (((((Relation.TransGen.single
    (DepStep.issue (p := .resolve) ⟨_, hpc⟩ hp0 (by simp) (by simp) (by simp) (by simp))).tail
    (DepStep.node (e := .async i .resolve) hp0)).tail
    (DepStep.stage (a := (.async i .resolve, true)) (c := (.async i (.write (.cta c)), false))
      (.inr ⟨rfl, rfl, rfl, hp0, hp1⟩))).tail
    (DepStep.node (e := .async i (.write (.cta c))) hp1)).tail
    (DepStep.stage (a := (.async i (.write (.cta c)), true))
      (c := (.async i (.notify (.cta c)), false))
      (.inr ⟨rfl, rfl, rfl, rfl, hp1, hp2⟩))).to_reflTransGen

/-- The leader's successful acknowledgement polls `0, …, s` guard its request numbered `s`. -/
theorem req_guard (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c s pc : Nat} {sp : Clc.Spec} {tg : List Nat}
    (he : X.get (producer L X c, reqIdx L X c s) = some ⟨pc, .clcIssue sp tg⟩) {cta : Nat}
    (hct : cta ∈ tg) (hcc : cta / 2 = c) {n : Nat} (hn : n ≤ s) :
    Resumes kernel X (epoll L X c n) (producer L X c, reqIdx L X c s) := by
  obtain ⟨-, -, -, hcb⟩ := issue_facts hpre hX ht he hct hcc
  obtain ⟨-, hcnt⟩ := req_spec he
  have hcnt' : issuesBefore L X c (producer L X c) (reqIdx L X c s) = s := hcnt
  rw [hcnt'] at hcb
  exact MbarRing.Poll.guard
    (fun w pc m q acq sc hw => ht.wait_spins (Frame.lt_of_get hX hw) hw)
    (List.getElem?_eq_some_iff.mp he).1 (by omega)

/-- An acknowledgement is an arrival on the acknowledgement barrier. -/
theorem ack_event {c : Nat} {b : Fin 10} {t : Nat} {e : Event}
    (he : X.get (ackEv L X c b t) = some e) :
    ∃ pc tx n rel sc, e = ⟨pc, .arrive ((slot L c).empty 0) tx n rel sc⟩ := by
  obtain ⟨hp, -⟩ := ack_spec he
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [sourceArrive] at hp
  subst hp
  exact ⟨_, _, _, _, _, rfl⟩

/-- Consumer `b`'s successful response polls `0, …, t` guard its acknowledgement numbered `t`. -/
theorem ack_guard (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {t : Nat} {e : Event}
    (he : X.get (ackEv L X c b t) = some e) {j : Nat} (hj : j ≤ t) :
    Resumes kernel X (fpoll L X c b j) (ackEv L X c b t) := by
  obtain ⟨-, hcnt⟩ := ack_spec he
  obtain ⟨pc, tx, n, rel, sc, rfl⟩ := ack_event he
  obtain ⟨-, hb⟩ := ack_thr hpre hX ht (thr_sel hpre c b) he
  have hcnt' : arrivals ((slot L c).empty 0) ((X.tr (thr L X c b)).take (ackIdx L X c b t)) = t :=
    hcnt
  rw [hcnt'] at hb
  exact MbarRing.Poll.guard
    (fun w pc m q acq sc hw => ht.wait_spins (Frame.lt_of_get hX hw) hw)
    (List.getElem?_eq_some_iff.mp he).1 (by omega)

/-! ### Object layer -/

/-- A counted completion's record: a completion of its request, after the first record. -/
theorem item_rec (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {i : Nat} {r : Record Ref}
    (hi : (X.objects ((slot L c).full f))[i]? = some r) {h ki cc : Nat}
    (hid : r.id = .async (h, ki) (.notify (.cta cc))) :
    r.action = .completeTx 16 ∧ ∃ q, phaseAt (X.objects ((slot L c).full f)) i = some q := by
  have ha : r.action = .completeTx 16 := by
    cases bar_source (b := ⟨.clc, 0, true⟩) hX ht Nat.one_pos (List.mem_of_getElem? hi) with
    | clc _ _ _ ha' => exact ha'
    | init _ _ hid' => rw [hid] at hid'; cases hid'
    | poll hid' => rw [hid] at hid'; cases hid'
    | arrive hid' => rw [hid] at hid'; cases hid'
    | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
    | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
  obtain ⟨s, hs⟩ := ring_state_at (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hi
    (ring_pos (b := ⟨.clc, 0, true⟩) hpre hX ht Nat.one_pos hi (by rw [ha]; intro n h; cases h))
  refine ⟨ha, s.phase, ?_⟩
  have hs' : stateBefore (X.objects ((slot L c).full f)) i = some s := hs
  simp [phaseAt, hs']

/-- A counted acknowledgement's record: a unit arrival, after the first record. -/
theorem ack_rec (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {i : Nat} {r : Record Ref}
    (hi : (X.objects ((slot L c).empty 0))[i]? = some r) {b : Fin 10} {t : Nat}
    (hid : r.id = .thread (ackEv L X c b t)) :
    r.action = .arrive 1 0 ∧ ∃ q, phaseAt (X.objects ((slot L c).empty 0)) i = some q := by
  have ha : r.action = .arrive 1 0 := by
    cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos (List.mem_of_getElem? hi) with
    | arrive _ _ ha' => exact ha'
    | init ha' _ hid' =>
      obtain ⟨-, -, pc, he⟩ := init_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos
        (List.mem_of_getElem? hi) ha'
      have heq := Ref.thread.inj (hid.symm.trans hid')
      rw [← heq] at he
      obtain ⟨pc', tx, n, rel, sc, he'⟩ := ack_event he
      cases he'
    | @poll g j pc p ok acq sc d hid' he =>
      have heq := Ref.thread.inj (hid.symm.trans hid')
      rw [← heq] at he
      obtain ⟨pc', tx, n, rel, sc', he'⟩ := ack_event he
      cases he'
    | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
    | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
    | clc hid' => rw [hid] at hid'; cases hid'
  obtain ⟨s, hs⟩ := ring_state_at (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hi
    (ring_pos (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hi (by rw [ha]; intro n h; cases h))
  refine ⟨ha, s.phase, ?_⟩
  have hs' : stateBefore (X.objects ((slot L c).empty 0)) i = some s := hs
  simp [phaseAt, hs']

/-- A thread's successful poll of a ring barrier with `n ≥ δ` earlier ones, of an alternating
poller: its record, which observed the phase before the one it found. -/
theorem poll_rec (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {b : Bar} (hb : b.Valid) {cta g n δ : Nat} (hδ : δ ≤ 1)
    (hδn : δ ≤ n) (halt : SelectedAlternates (objectThreadSelected g) (X.objects (b.loc L cta)) δ)
    (h : n < okPolls (b.loc L cta) (X.tr g)) :
    ∃ i w st, (X.objects (b.loc L cta))[i]? = some w ∧
      w.id = .thread (g, MbarRing.Poll.nth X (b.loc L cta) g n) ∧ w.reply.waited = some true ∧
      selectedBefore (objectThreadSelected g) (X.objects (b.loc L cta)) i = n ∧
      stateBefore (X.objects (b.loc L cta)) i = some st ∧ 0 < st.phase ∧
      observedAt (X.objects (b.loc L cta)) i = some (st.phase - 1) := by
  obtain ⟨i, w, p, hi, hwid, -, hww, -, hc⟩ :=
    MbarRing.Poll.record hX (poll_clean hpre hX ht hb) h
  obtain ⟨st, hst, hpos, ho⟩ := MbarRing.Poll.observed_some (hX.tma.2.2.1 _).1
      (objects_noInval hX ht _) hδ halt hi
    (objectThreadSelected_iff.mpr ⟨_, hwid⟩) hww (by omega)
  exact ⟨i, w, st, hi, hwid, hww, hc, hst, hpos, ho⟩

/-- An acknowledgement record of the acknowledgement barrier: consumer `b`'s acknowledgement
numbered by its earlier arrivals. -/
theorem ack_of_arrival (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {r : Record Ref} (hr : r ∈ X.objects ((slot L c).empty 0))
    {n tx : Nat} (ha : r.action = .arrive n tx) :
    ∃ b t, r.id = .thread (ackEv L X c b t) := by
  cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos hr with
  | @arrive g jj pc rel sc d hid he ha' hσ hby hcta =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨rr, rfl⟩ := Bar.role_of (.inr (.inl hby))
    have hrw := ht.role_warp hg (idx_le he) hσ
    simp only [Bar.arriveCta, Bar.arriveLeader, ↓reduceIte] at hcta
    obtain ⟨b, hsel⟩ := sel_of_ack (c := c) hpre hby hrw (by omega)
    obtain ⟨hgt, -⟩ := ack_thr hpre hX ht hsel he
    subst hgt
    refine ⟨b, ((X.tr (thr L X c b)).take jj).countP (ackP L c), ?_⟩
    rw [hid]
    have := nthEv_eq (p := ackP L c) he (by simp [sourceArrive]; rfl)
    simp only [ackEv, ackIdx, this]
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
  | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
  | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby

/-- A completion record of response barrier `f`: the item of its request's number. -/
theorem item_of_completion (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {f : Fin 2} {r : Record Ref}
    (hr : r ∈ X.objects ((slot L c).full f)) {n : Nat} (ha : r.action = .completeTx n) :
    ∃ s, r.id = item L X c f s := by
  cases bar_source (b := ⟨.clc, 0, true⟩) hX ht Nat.one_pos hr with
  | @clc h jj pc cc sp tg d hid he htg ha' hσ hby hmb hcta hcl =>
    obtain ⟨hp, hmb', -, -⟩ := issue_facts hpre hX ht he htg (show cc / 2 = c by omega)
    subst hp
    refine ⟨((X.tr (producer L X c)).take jj).countP (reqP L c), ?_⟩
    rw [hid]
    have := nthEv_eq (p := reqP L c) he (by simp [clcIssuesTo, hmb'])
    simp only [item, reqIdx, this, ← hcta]
  | init ha' => rw [ha] at ha'; cases ha'
  | poll _ _ ha' => rw [ha] at ha'; cases ha'
  | arrive _ _ ha' => rw [ha] at ha'; cases ha'
  | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
  | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby

/-- The completed phase consumer `b`'s response poll with `j` earlier ones observed. -/
abbrev oF (L : Launch) (X : Execution) (c : Nat) (b : Fin 10) (j : Nat) : Nat :=
  MbarRing.Poll.observedOf X ((slot L c).full ((slot L c).owner b)) (.thread (fpoll L X c b j))

/-- The completed phase the leader's acknowledgement poll with `n` earlier ones observed. -/
abbrev oE (L : Launch) (X : Execution) (c n : Nat) : Nat :=
  MbarRing.Poll.observedOf X ((slot L c).empty 0) (.thread (epoll L X c n))

/-- The phase of a counted completion. -/
abbrev phF (L : Launch) (X : Execution) (c : Nat) (f : Fin 2) (x : Fin 1 × Nat) : Nat :=
  MbarRing.Poll.phaseOf X ((slot L c).full f) (item L X c f x.2)

/-- The phase of a counted acknowledgement. -/
abbrev phE (L : Launch) (X : Execution) (c : Nat) (y : Fin 10 × Nat) : Nat :=
  MbarRing.Poll.phaseOf X ((slot L c).empty 0) (.thread (ackEv L X c y.1 y.2))

/-- Consumer `b`'s present response poll with `j` earlier ones: its record, which observed the
phase before the one it found. -/
theorem fpoll_rec (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {b : Fin 10} {j : Nat}
    (hp : X.RefPresent (.thread (fpoll L X c b j))) :
    ∃ i w st, (X.objects ((slot L c).full ((slot L c).owner b)))[i]? = some w ∧
      w.id = .thread (fpoll L X c b j) ∧ w.reply.waited = some true ∧
      selectedBefore (objectThreadSelected (thr L X c b))
        (X.objects ((slot L c).full ((slot L c).owner b))) i = j ∧
      stateBefore (X.objects ((slot L c).full ((slot L c).owner b))) i = some st ∧
      0 < st.phase ∧ oF L X c b j = st.phase - 1 ∧
      observedAt (X.objects ((slot L c).full ((slot L c).owner b))) i = some (st.phase - 1) := by
  have hn := MbarRing.Poll.nth_present.mp hp
  obtain ⟨i, w, st, hi, hwid, hww, hc, hst, hpos, ho⟩ := poll_rec (b := ⟨.clc, 0, true⟩)
    (cta := 2 * c + ((slot L c).owner b).val) hpre hX ht Nat.one_pos (δ := 0) (by omega)
    (Nat.zero_le _) (resp_alt hpre hX ht _ _) hn
  refine ⟨i, w, st, hi, hwid, hww, hc, hst, hpos, ?_, ho⟩
  have := MbarRing.Poll.observedOf_eq hX hi ho
  rw [hwid] at this
  exact this

/-- The leader's present acknowledgement poll with `n ≥ 1` earlier ones: its record, which
observed the phase before the one it found. -/
theorem epoll_rec (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c n : Nat} (hn1 : 1 ≤ n)
    (hp : X.RefPresent (.thread (epoll L X c n))) :
    ∃ i w st, (X.objects ((slot L c).empty 0))[i]? = some w ∧
      w.id = .thread (epoll L X c n) ∧ w.reply.waited = some true ∧
      selectedBefore (objectThreadSelected (producer L X c)) (X.objects ((slot L c).empty 0)) i =
        n ∧
      stateBefore (X.objects ((slot L c).empty 0)) i = some st ∧
      0 < st.phase ∧ oE L X c n = st.phase - 1 ∧
      observedAt (X.objects ((slot L c).empty 0)) i = some (st.phase - 1) := by
  have hn := MbarRing.Poll.nth_present.mp hp
  obtain ⟨i, w, st, hi, hwid, hww, hc, hst, hpos, ho⟩ := poll_rec (b := ⟨.clc, 0, false⟩)
    (cta := 2 * c) hpre hX ht Nat.one_pos (δ := 1) le_rfl hn1 (ack_alt hpre hX ht _ _) hn
  refine ⟨i, w, st, hi, hwid, hww, hc, hst, hpos, ?_, ho⟩
  have := MbarRing.Poll.observedOf_eq hX hi ho
  rw [hwid] at this
  exact this

/-- **Cluster `c`'s response ring.** -/
def ring (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (c : Nat) : MbarRing.Items.Ring L kernel Prod X 1 10 2 (fun _ => 1) where
  owner := (slot L c).owner
  ownF _ _ := 0
  wE _ n := epoll L X c n
  opF _ _ s := (producer L X c, reqIdx L X c s)
  itF f _ s := item L X c f s
  wF b j := fpoll L X c b j
  cm b t := ackEv L X c b t
  note b _ t := .thread (ackEv L X c b t)
  SF f := SF L X c f
  phF f x := phF L X c f x
  SE _ := SE L X c
  phE _ y := phE L X c y
  oF b j := oF L X c b j
  oE _ n := oE L X c n
  cover _ _ := ⟨0, Subsingleton.elim _ _⟩
  guardP f x hx n _ hn := by
    obtain ⟨r, hr, hid, -⟩ := (mem_SF hX).mp hx
    obtain ⟨sp, tg, hci, hct, -, -⟩ := hX.clc_notified hr hid
    obtain ⟨pc, he⟩ := hci
    exact req_guard hpre hX ht he hct (by omega) hn
  issueF f x hx := by
    obtain ⟨r, hr, hid, -⟩ := (mem_SF hX).mp hx
    obtain ⟨sp, tg, hci, -, hnot, -⟩ := hX.clc_notified hr hid
    exact clc_reach hX hci hnot
  guardM _ y hy j hj := by
    obtain ⟨r, hr, hid, -⟩ := (mem_SE hX).mp hy
    obtain ⟨ev, he⟩ : X.RefPresent (.thread (ackEv L X c y.1 y.2)) :=
      hid ▸ object_record_present hX.tma hr
    exact ack_guard hpre hX ht he hj
  issue _ _ _ := .refl
  obsF b j hp x hx hph := by
    obtain ⟨i, w, st, hi, hwid, hww, -, -, -, ho, hoi⟩ := fpoll_rec hpre hX ht hp
    obtain ⟨r, hr, hid, hrf⟩ := (mem_SF hX).mp hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨ha, q, hq⟩ := item_rec hpre hX ht hk hid
    have h1 := MbarRing.Poll.phaseOf_eq hX hk hq
    rw [hid] at h1
    have hqe : q = st.phase - 1 := by
      have : phF L X c ((slot L c).owner b) x = oF L X c b j := hph
      simp only [phF] at this h1
      rw [← h1, this, ho]
    rw [hqe] at hq
    have := hX.observed_of_phase (objects_noInval hX ht _) hk hrf
        (by rw [ha]; trivial) hi hww hq hoi
    rw [hid, hwid] at this
    exact Witness.of_mbarObserved this
  obsE _ n hn1 hp y hy hph := by
    obtain ⟨i, w, st, hi, hwid, hww, -, -, -, ho, hoi⟩ := epoll_rec hpre hX ht hn1 hp
    obtain ⟨r, hr, hid, hrf⟩ := (mem_SE hX).mp hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨ha, q, hq⟩ := ack_rec hpre hX ht hk hid
    have h1 := MbarRing.Poll.phaseOf_eq hX hk hq
    rw [hid] at h1
    have hqe : q = st.phase - 1 := by
      have : phE L X c y = oE L X c n := hph
      simp only [phE] at this h1
      rw [← h1, this, ho]
    rw [hqe] at hq
    have := hX.observed_of_phase (objects_noInval hX ht _) hk hrf
        (by rw [ha]; trivial) hi hww hq hoi
    rw [hid, hwid] at this
    exact Witness.of_mbarObserved this
  fullF b j hp := by
    classical
    obtain ⟨i, w, st, hi, hwid, hww, -, hst, hpos, ho, -⟩ := fpoll_rec hpre hX ht hp
    have hil : i ≤ (X.objects ((slot L c).full ((slot L c).owner b))).length :=
      (List.getElem?_eq_some_iff.mp hi).1.le
    obtain ⟨k, r, n, -, hk, hrf, ha, hq⟩ :=
      (resp_unitTx hpre hX ht (2 * c + ((slot L c).owner b).val)).completion_in_phase
        (by norm_num) (hX.tma.2.2.1 _).1 (objects_noInval hX ht _) hil hst (q := st.phase - 1)
            (by omega)
    obtain ⟨s, hid⟩ := item_of_completion hpre hX ht (List.mem_of_getElem? hk) ha
    have hmem : ((0 : Fin 1), s) ∈ SF L X c ((slot L c).owner b) :=
      (mem_SF hX).mpr ⟨r, List.mem_of_getElem? hk, hid, hrf⟩
    have h1 := MbarRing.Poll.phaseOf_eq hX hk hq
    rw [hid] at h1
    refine Finset.card_pos.mpr ⟨((0 : Fin 1), s), Finset.mem_filter.mpr ⟨hmem, ?_⟩⟩
    show phF L X c ((slot L c).owner b) (0, s) = oF L X c b j
    rw [ho]
    exact h1
  fullE _ n hn1 hp := by
    classical
    obtain ⟨i, w, st, hi, hwid, hww, -, hst, hpos, ho, -⟩ := epoll_rec hpre hX ht hn1 hp
    have hil : i ≤ (X.objects ((slot L c).empty 0)).length :=
      (List.getElem?_eq_some_iff.mp hi).1.le
    have hcard := (hX.tma.2.2.1 ((slot L c).empty 0)).1.card_unit_arrivals_phase
        (objects_noInval hX ht ((slot L c).empty 0)) (n := 10)
      (q := st.phase - 1)
      (fun k r c' tx hk _ ha => by
        cases bar_source (b := ⟨.clc, 0, false⟩) hX ht Nat.one_pos (List.mem_of_getElem? hk) with
        | arrive _ _ ha' => rw [ha] at ha'; cases ha'; rfl
        | init ha' => rw [ha] at ha'; cases ha'
        | poll _ _ ha' => rw [ha] at ha'; cases ha'
        | copy _ _ _ _ _ hby => simp [Bar.copyBy] at hby
        | notify _ _ _ _ _ hby => simp [Bar.commitBy] at hby
        | clc _ _ _ _ _ hby => simp [Bar.clcBy] at hby)
      (fun k s _ hs => ring_expected (b := ⟨.clc, 0, false⟩) hpre hX ht Nat.one_pos hs)
      (incrementsBefore_zero hX ht _) hil hst (by omega)
    let pos : Fin 10 × Nat → Nat := fun y =>
      ((X.objects ((slot L c).empty 0)).findIdx?
        (fun r => decide (r.id = .thread (ackEv L X c y.1 y.2)))).getD 0
    have hsub : (Finset.range (X.objects ((slot L c).empty 0)).length).filter
        (fun k => UnitArrivalIn (X.objects ((slot L c).empty 0)) (st.phase - 1) k) ⊆
        ((SE L X c).filter (fun y => phE L X c y = oE L X c n)).image pos := by
      intro k hk
      obtain ⟨-, r, tx, hk', ha, hrf, hq⟩ := Finset.mem_filter.mp hk
      obtain ⟨b, t, hid⟩ := ack_of_arrival hpre hX ht (List.mem_of_getElem? hk') ha
      have hmem : (b, t) ∈ SE L X c := (mem_SE hX).mpr ⟨r, List.mem_of_getElem? hk', hid, hrf⟩
      have h1 := MbarRing.Poll.phaseOf_eq hX hk' hq
      rw [hid] at h1
      refine Finset.mem_image.mpr ⟨(b, t), Finset.mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
      · show MbarRing.Poll.phaseOf X _ _ = MbarRing.Poll.observedOf X _ _
        rw [h1]
        exact ho.symm
      · have := MbarRing.Poll.findIdx_of_get hX hk'
        rw [hid] at this
        simp only [pos, this, Option.getD_some]
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    omega
  ltF b j j' hjj hp := by
    have hn := MbarRing.Poll.nth_present.mp hp
    refine ⟨MbarRing.Poll.nth_present.mpr (by omega), ?_⟩
    exact MbarRing.Poll.observed_lt (δ := 0) hX (Nat.zero_le 1) (poll_clean (b := ⟨.clc, 0, true⟩)
      hpre hX ht Nat.one_pos) (objects_noInval hX ht _) (resp_alt hpre hX ht _
        (2 * c + ((slot L c).owner b).val))
      (Nat.zero_le _) hjj hn
  ltE _ n n' hn1 hnn hp := by
    have hn := MbarRing.Poll.nth_present.mp hp
    refine ⟨MbarRing.Poll.nth_present.mpr (by omega), ?_⟩
    exact MbarRing.Poll.observed_lt (δ := 1) hX le_rfl (poll_clean (b := ⟨.clc, 0, false⟩)
      hpre hX ht Nat.one_pos) (objects_noInval hX ht _) (ack_alt hpre hX ht _ (2 * c)) hn1 hnn hn

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
