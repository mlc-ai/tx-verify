-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.AckBlocker
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.AckExit
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.AckCount
public import Kernels.Fp16Gemm8192.Proof.Protocol.Elected

@[expose] public section

/-! # The leader scheduler's acknowledgement wait is blocked by an acknowledging thread

At a failed acknowledgement poll of the leader scheduler `g`, with `N` successful response polls
(`ack_pigeonhole`: `N` successful acknowledgement polls, and one selector `f` has delivered `N - 1`
arrivals), some thread `b` of selector `f` has arrived fewer than `N` times and is not in its exit
stage, or has stopped without its exit. The candidate `b` is the elected lane of `f`'s warp (or the
warp's first lane when no lane of it has an election event, see `ElectedOrIdle`). Its arrivals are
at most the selector's (`ack_arrivals_le`). If `b` were in an exit stage, it would have read a
response that claims no CTA after a successful response poll, at a count beyond the scheduler's
(`noclaim_lt`), so its arrivals would be at least `N`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread's election events return its own lane: the warp's collective leader is the thread's
lane, or the thread has no election event. -/
def ElectedOrIdle (L : Launch) (X : Execution) (b : Nat) : Prop :=
  ∀ j pc mask inst leader, X.get (b, j) = some ⟨pc, .elect mask inst leader⟩ → leader = laneOf L b

theorem countP_take_mono {α : Type} (p : α → Bool) (es : List α) {j k : Nat} (h : j ≤ k) :
    (es.take j).countP p ≤ (es.take k).countP p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.countP_append]
  omega

theorem okPolls_take_mono (m : Loc) (es : List Event) {j k : Nat} (h : j ≤ k) :
    okPolls m (es.take j) ≤ okPolls m (es.take k) :=
  countP_take_mono _ es h

theorem arrivals_take_mono (m : Loc) (es : List Event) {j k : Nat} (h : j ≤ k) :
    arrivals m (es.take j) ≤ arrivals m (es.take k) :=
  countP_take_mono _ es h

/-- Counting one more event of a trace: the successful polls of its prefix grow by the event. -/
theorem okPolls_take_succ {m : Loc} {es : List Event} {j : Nat} {e : Event} (he : es[j]? = some e) :
    Flow.okPolls m (es.take (j + 1)) =
      Flow.okPolls m (es.take j) + (if Flow.okPoll m e = true then 1 else 0) := by
  rw [List.take_add_one, he]
  simp [Flow.okPolls, List.countP_append]

/-- The candidate of selector `f` of cluster `c`: a thread of the selector's warp that is elected,
or the warp's first lane when no lane of the warp has an election event. The warp's first lane
(`base`) is a member of the selector. -/
theorem ack_candidate (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hT : ThreadFacts L X) {c : Nat} (f : Fin 10) (hc : 2 * c + 1 < L.grid) :
    ∃ b, b < L.threads ∧ ClcRing.consumerSel L c f b = true ∧
      (ClcRing.laneZero f = true ∨ ElectedOrIdle L X b) := by
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hc' : 2 * c + 1 < 1024 := by rw [← hgrid]; exact hc
  have ht := ClcRing.ctaOf_lt f
  have hw : ClcRing.warpOf f < 12 := by
    unfold ClcRing.warpOf
    fin_cases f <;> simp
  set base := (2 * c + ClcRing.ctaOf f) * L.block + 32 * ClcRing.warpOf f with hbase
  have hbt : base < L.threads := by
    unfold Launch.threads
    rw [hgrid, hblock, hbase, hblock]
    omega
  have hsel_base : ClcRing.consumerSel L c f base = true := by
    simp only [ClcRing.consumerSel, decide_eq_true_eq]
    rw [hbase, hblock]
    refine ⟨by omega, by omega, fun _ => by omega⟩
  by_cases hz : ClcRing.laneZero f = true
  · exact ⟨base, hbt, hsel_base, Or.inl hz⟩
  · by_cases hx : ∃ x, x < L.threads ∧ ClcRing.consumerSel L c f x = true ∧
        ∃ j pc mask inst leader, X.get (x, j) = some ⟨pc, .elect mask inst leader⟩
    · obtain ⟨x, hxt, hxs, j, pc, mask, inst, leader, hev⟩ := hx
      obtain ⟨h, j', hh, hsw, hel'⟩ := elected_of_elect hpre hX (X := X) hev
      refine ⟨h, hh, ?_, Or.inr ?_⟩
      · simp only [ClcRing.consumerSel, decide_eq_true_eq] at hxs ⊢
        obtain ⟨h1, h2, -⟩ := hxs
        obtain ⟨⟨-, -, hcta⟩, hwarp⟩ := hsw
        refine ⟨?_, ?_, fun hz' => absurd hz' hz⟩
        · rw [← hcta]
          exact h1
        · rw [← hwarp]
          exact h2
      · intro j'' pc'' mask'' inst'' leader'' hel''
        have hj := hT.elect_once hh hel'' hel'
        subst hj
        have hsame : leader'' = laneOf L h := by
          have e1 : X.get (h, j'') = some ⟨pc'', .elect mask'' inst'' leader''⟩ := hel''
          have e2 : X.get (h, j'') = some ⟨pc, .elect mask inst (laneOf L h)⟩ := hel'
          rw [e1] at e2
          cases Option.some.inj e2
          rfl
        exact hsame
    · refine ⟨base, hbt, hsel_base, Or.inr ?_⟩
      intro j pc mask inst leader hev
      exact absurd ⟨base, hbt, hsel_base, j, pc, mask, inst, leader, hev⟩ hx

/-- An exit stage holds no response: the held count is zero. -/
theorem clcHeld_of_exitOff {d : ThreadD} (h : d.exitOff ≠ none) : d.clcHeld = 0 := by
  rcases d with p | (l | m | s | c)
  · rfl
  · obtain ⟨site, mm, n, q, cp, r, x⟩ := l
    cases site <;> simp_all [ThreadD.clcHeld, ThreadD.exitOff, Loader.exitOff]
  · obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
    cases site <;> simp_all [ThreadD.clcHeld, ThreadD.exitOff, Mma.exitOff]
  · obtain ⟨site, ap, cp, r, x⟩ := s
    cases site <;> simp_all [ThreadD.clcHeld, ThreadD.exitOff, Scheduler.exitOff]
  · obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
    cases site <;> simp_all [ThreadD.clcHeld, ThreadD.exitOff, Consumer.exitOff]

/-- A selector of the consumers' laneZero kind lies in a consumer warp. -/
theorem warpOf_lt8_of_laneZero (f : Fin 10) (h : ClcRing.laneZero f = true) : ClcRing.warpOf f <
    8 := by
  revert h
  revert f
  decide

/-- A thread of an acknowledging warp (8 to 11) is elected or idle, as its selector is not a
lane-zero consumer. -/
theorem electedOrIdle_of (hbsel : ClcRing.consumerSel L c f b = true)
    (hbc : ClcRing.laneZero f = true ∨ ElectedOrIdle L X b) (h8 : 8 ≤ b % L.block / 32) :
    ElectedOrIdle L X b := by
  rcases hbc with hz | hEO
  · exfalso
    have hw := warpOf_lt8_of_laneZero f hz
    simp only [ClcRing.consumerSel, decide_eq_true_eq] at hbsel
    omega
  · exact hEO

/-- An elected or idle thread has no election event outside its own lane. -/
theorem not_electOut_of (hEO : ElectedOrIdle L X b) (k : Nat) : ¬ ElectOut L b ((X.tr b).take k) :=
    by
  rintro ⟨i, e, he, x, y, leader, hk, hne⟩
  obtain ⟨pc, kind⟩ := e
  have hget : X.get (b, i) = some ⟨pc, kind⟩ := by
    change (X.tr b)[i]? = _
    rw [List.getElem?_take] at he
    split_ifs at he with hi
    exact he
  simp only at hk
  subst hk
  exact hne (hEO i pc x y leader hget)

/-- **The contradiction of an exit stage.** A thread in an exit stage at `k` whose last successful
response poll before `k` is followed by a read of a response that claims no CTA has at least the
scheduler's acknowledgement count of arrivals, which is more than its arrivals. -/
theorem ack_contra (ht : ThreadFacts L X) (hag : AllResponsesAgree L X) {g b : Nat}
    (hg : g < L.threads) (hb : b < L.threads) (hcl : g / L.block / 2 = b / L.block / 2)
    {sd : Scheduler.D}
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))))
    (hsd : sd.site = .ackWait)
    (hgpoll : ∀ j pc p acq sc,
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      j + 1 < (X.tr g).length)
    (harr : arrivals (clcAck L b) (X.tr b) <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g))
    (hsel : ∃ f, ClcRing.consumerSel L (b / L.block / 2) f b = true)
    {k : Nat} {d : ThreadD} (hk : k ≤ (X.tr b).length)
    (hσk : Frame.stateAt (code L) X b k = some (some d)) (hex : d.exitOff ≠ none)
    {j pc p : Nat} {acq : Bool} {sc : MbarScope} {pcr : Nat} {src : Acc} {bs : List (Option Byte)}
    {rr : ClcResponse} (hjk : j + 1 < k)
    (hbw : (X.tr b)[j]? = some ⟨pc, .wait (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩)
    (hbr : (X.tr b)[j + 1]? = some ⟨pcr, .rd src bs⟩)
    (hbsrc : src.SameFootprint ⟨⟨.shared, b / L.block, L.sharedBase + 144⟩, 16, false, false, .cta,
      0, false⟩)
    (hrr : Flow.responseOf bs = some rr) (hnc : ¬ Loader.claims rr) : False := by
  have hlt := noclaim_lt ht hag hg hcl hσg hsd hgpoll hbw hbr hbsrc hrr hnc
  have hack : okPolls (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) ((X.tr b).take k) =
      arrivals (clcAck L b) ((X.tr b).take k) + d.clcHeld :=
    ht.ack_exact hb hsel hk hσk
  have hheld : d.clcHeld = 0 := clcHeld_of_exitOff hex
  have hsucc : okPolls (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) ((X.tr b).take (j + 1)) =
      okPolls (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) ((X.tr b).take j) + 1 := by
    rw [okPolls_take_succ hbw]
    simp [Flow.okPoll, sourceWaitSuccess]
  have hpolls := okPolls_take_mono (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) (X.tr b)
    (show j + 1 ≤ k by omega)
  have hmono : arrivals (clcAck L b) ((X.tr b).take k) ≤
      arrivals (clcAck L b) (X.tr b) := by
    have h := arrivals_take_mono (clcAck L b) (X.tr b) hk
    rwa [List.take_length] at h
  omega

/-- A no-claim query of the trace is preceded by a successful response poll and the read of the
response it reports. -/
theorem noclaim_of_query (ht : ThreadFacts L X) {b k : Nat} (hb : b < L.threads)
    (hq : NoClaimQ ((X.tr b).take k)) :
    ∃ (j pc p : Nat) (acq : Bool) (sc : MbarScope) (pcr : Nat) (src : Acc)
      (bs : List (Option Byte)) (rr : ClcResponse), j + 1 < k ∧
      (X.tr b)[j]? = some ⟨pc, .wait (Bar.loc L (b / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      (X.tr b)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, b / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr := by
  obtain ⟨i, e, hi, q, r, hk, hnc⟩ := hq
  have hik : i < k := by
    rcases (List.getElem?_eq_some_iff.mp hi) with ⟨h1, -⟩
    simp only [List.length_take] at h1
    omega
  have hget : (X.tr b)[i]? = some e := by
    rw [List.getElem?_take] at hi
    split_ifs at hi
    exact hi
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  obtain ⟨j, pc', p, acq, sc, pcr, src, bs, hj2, hw, hr, hsf, hres⟩ :=
    noClaim_before ht hb (i := i) (pc := pc) (q := q) (r := r) (show X.get (b, i) = _ from hget)
  exact ⟨j, pc', p, acq, sc, pcr, src, bs, r, by omega, hw, hr, hsf, hres, hnc⟩

/-- A warp of selector 8 or 9 is the leader CTA's: its selector's CTA is zero. -/
theorem ctaOf_of_warp89 : ∀ f : Fin 10, (ClcRing.warpOf f = 8 ∨ ClcRing.warpOf f = 9) →
    ClcRing.ctaOf f = 0 := by decide

/-- **A selected thread outside the exit stage.** A thread `b` of a selector of cluster `g`'s, with
fewer arrivals on the acknowledgement barrier than `g`'s successful response polls, is not in an
exit stage at its trace's end, or has stopped without its exit: an exit stage (or a stop after the
exit) has a no-claim read after a successful poll, which gives at least as many arrivals
(`ack_contra`). -/
theorem ack_nonexit (ht : ThreadFacts L X)
    (hag : AllResponsesAgree L X) {g b : Nat} {f : Fin 10}
    (hg : g < L.threads) (hb : b < L.threads) (hcl : g / L.block / 2 = b / L.block / 2)
    (hbsel : ClcRing.consumerSel L (g / L.block / 2) f b = true)
    (hbc : ClcRing.laneZero f = true ∨ ElectedOrIdle L X b)
    {sd : Scheduler.D}
    (hσg : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))))
    (hsd : sd.site = .ackWait)
    (hgpoll : ∀ j pc p acq sc,
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      j + 1 < (X.tr g).length)
    (harr : arrivals (clcAck L b) (X.tr b) <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) :
    (∃ d, Frame.stateAt (code L) X b (X.tr b).length = some (some d) ∧ d.exitOff = none) ∨
      (Frame.stateAt (code L) X b (X.tr b).length = none ∧ ∀ pc', (X.tr b).getLast? ≠
        some ⟨pc', .exit⟩) := by
  have hsel : ∃ f', ClcRing.consumerSel L (b / L.block / 2) f' b = true :=
    ⟨f, by rw [← hcl]; exact hbsel⟩
  have hsel' := hbsel
  simp only [ClcRing.consumerSel, decide_eq_true_eq] at hsel'
  by_contra hcon
  obtain ⟨k, hk, hkend, d, hσk, hex⟩ : ∃ k, k ≤ (X.tr b).length ∧
      (k = (X.tr b).length ∨ (k + 1 = (X.tr b).length ∧ ∃ pc, X.get (b, k) = some ⟨pc, .exit⟩)) ∧
      ∃ d, Frame.stateAt (code L) X b k = some (some d) ∧ d.exitOff ≠ none := by
    rcases hs : Frame.stateAt (code L) X b (X.tr b).length with _ | o
    · obtain ⟨pc', hl⟩ : ∃ pc', (X.tr b).getLast? = some ⟨pc', .exit⟩ := by
        by_contra hnx
        exact hcon (Or.inr ⟨hs, fun pc' h => hnx ⟨pc', h⟩⟩)
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
      have hget : X.get (b, ys.length) = some ⟨pc', .exit⟩ := by
        change (X.tr b)[ys.length]? = _
        rw [hys]
        simp
      have hlen : (X.tr b).length = ys.length + 1 := by rw [hys]; simp
      obtain ⟨d, hd, hdx⟩ := ht.exit_event_state hb hget
      exact ⟨ys.length, by omega, Or.inr ⟨by omega, pc', hget⟩, d, hd, hdx⟩
    · cases o with
      | none => exact absurd hs (ht.tracked b _ hb)
      | some d =>
        by_cases hdx : d.exitOff = none
        · exact absurd (Or.inl ⟨d, hs, hdx⟩) hcon
        · exact ⟨(X.tr b).length, le_rfl, Or.inl rfl, d, hs, hdx⟩
  have hkexit : ∀ pe, k + 1 = (X.tr b).length → X.get (b, k) = some pe → k < (X.tr b).length :=
    fun _ h _ => by omega
  rcases d with p | (l | m | s' | c)
  · simp [ThreadD.exitOff] at hex
  · -- the loader
    have hw := ht.role_warp hb hk hσk
    simp only [roleWarp] at hw
    have hw11 : b % L.block / 32 = 11 := hw
    have hEO := electedOrIdle_of hbsel hbc (by omega)
    have hsite : l.site = .exitArrive ∨ l.site = .exitWait ∨ l.site = .exit := by
      obtain ⟨site, mm, n, q, cp, r, x⟩ := l
      cases site <;> simp [ThreadD.exitOff, Loader.exitOff] at hex ⊢
    have hq := (ht.loader_exit_query hb hσk).1 (by rcases hsite with h | h | h <;> simp [h])
    rcases hq with hNC | hEx
    · obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hjk, h1, h2, h3, h4, h5⟩ :=
        noclaim_of_query ht hb hNC
      exact ack_contra ht hag hg hb hcl hσg hsd hgpoll harr hsel hk hσk hex hjk h1 h2 h3 h4 h5
    · exact absurd hEx (not_electOut_of hEO k)
  · -- the MMA warp
    have hw := ht.role_warp hb hk hσk
    simp only [roleWarp] at hw
    have heven : b / L.block % 2 = 0 := by
      have h89 : ClcRing.warpOf f = 8 ∨ ClcRing.warpOf f = 9 := by omega
      have hc0 := ctaOf_of_warp89 f h89
      omega
    by_cases hE : ∃ j pc mask inst leader, X.get (b, j) = some ⟨pc, .elect mask inst leader⟩
    · obtain ⟨j, pc, mask, inst, leader, hel⟩ := hE
      have hlead := electedOrIdle_of hbsel hbc (by omega) j pc mask inst leader hel
      have hel' : X.Elect (b, j) pc mask inst (laneOf L b) := by
        unfold Execution.Elect
        rw [← hlead]
        exact hel
      rcases ht.mma_leader hb heven (by omega) hel' with hA | hB | hC
      · obtain ⟨m', hm, hx, -⟩ := hA
        exact hcon (Or.inl ⟨.inr (.mma m'), hm, hx⟩)
      · obtain ⟨-, j', pc', p', acq', sc', pcr', src', bs', rr', hl, h1, h2, h3, h4, h5⟩ := hB
        have hlt : j' + 1 < (X.tr b).length := (List.getElem?_eq_some_iff.mp h2).1
        have hjk : j' + 1 < k := by
          rcases hkend with rfl | ⟨hk1, pe, hpe⟩
          · exact hlt
          · have hne : j' + 1 ≠ k := by
              intro hjk
              rw [hjk] at h2
              have : X.get (b, k) = some ⟨pcr', .rd src' bs'⟩ := h2
              rw [hpe] at this
              cases this
            omega
        exact ack_contra ht hag hg hb hcl hσg hsd hgpoll harr hsel hk hσk hex hjk h1 h2 h3 h4 h5
      · obtain ⟨hC1, hC2⟩ := hC
        rcases hkend with rfl | ⟨hk1, pe, hpe⟩
        · rw [hσk] at hC1
          cases hC1
        · have hl : (X.tr b).getLast? = some ⟨pe, .exit⟩ := by
            rw [List.getLast?_eq_getElem?]
            have hlast : (X.tr b).length - 1 = k := by omega
            rw [hlast]
            exact hpe
          exact hC2 pe hl
    · obtain ⟨d', hd', hdx', -⟩ := ht.mma_unelected hb heven (by omega)
        (fun j pc mask inst leader h => hE ⟨j, pc, mask, inst, leader, h⟩)
      exact hcon (Or.inl ⟨d', hd', hdx'⟩)
  · -- the scheduler
    have hw := ht.role_warp hb hk hσk
    simp only [roleWarp] at hw
    have hw10 : b % L.block / 32 = 10 := hw
    have hEO := electedOrIdle_of hbsel hbc (by omega)
    have hsite : s'.site = .exitArrive ∨ s'.site = .exitWait ∨ s'.site = .exit := by
      obtain ⟨site, ap, cp, r, x⟩ := s'
      cases site <;> simp [ThreadD.exitOff, Scheduler.exitOff] at hex ⊢
    have hq := (ht.sched_exit_query hb hσk).1 (by rcases hsite with h | h | h <;> simp [h])
    rcases hq with hNC | hEx
    · obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hjk, h1, h2, h3, h4, h5⟩ :=
        noclaim_of_query ht hb hNC
      exact ack_contra ht hag hg hb hcl hσg hsd hgpoll harr hsel hk hσk hex hjk h1 h2 h3 h4 h5
    · exact absurd hEx (not_electOut_of hEO k)
  · -- the consumer
    have hw := ht.role_warp hb hk hσk
    simp only [roleWarp] at hw
    rcases hkend with rfl | ⟨hk1, pe, hpe⟩
    · obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, h1, h2, h3, h4, h5⟩ :=
        ht.cons_exit_read hb hσk hex
      have hjk : j + 1 < (X.tr b).length := (List.getElem?_eq_some_iff.mp h2).1
      exact ack_contra ht hag hg hb hcl hσg hsd hgpoll harr hsel hk hσk hex hjk h1 h2 h3 h4 h5
    · obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hjk, h1, h2, h3, h4, h5⟩ :=
        ht.consumer_exit hb hpe hσk rfl (by omega)
      exact ack_contra ht hag hg hb hcl hσg hsd hgpoll harr hsel hk hσk hex hjk h1 h2 h3 h4 h5

/-- **The leader scheduler's acknowledgement wait is blocked** (`AckBlocked`): at a failed
acknowledgement poll, some thread of a selector has arrived fewer times than the scheduler's
successful polls, and it is not in an exit stage. -/
theorem ack_blocked_proved (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hub : ∀ g k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩)
    (hag : AllResponsesAgree L X) :
    AckBlocked L X := by
  intro g pc p acq sc before hg hlead hwarp hlast hstate hpar
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (X.tr g).length = ys.length + 1 := by rw [hys]; simp
  have hys' : (X.tr g).take ys.length = ys := by rw [hys]; simp
  have hgk : X.get (g, ys.length) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) p
      false acq sc⟩ := by
    change (X.tr g)[ys.length]? = _
    rw [hys]
    simp
  obtain ⟨r, hσ0, hrw⟩ := wait_role hX ht (Frame.lt_of_get hX hgk) hgk rfl
  obtain ⟨s, rfl⟩ : ∃ s, r = .sched s := by
    cases r with
    | loader l => simp [roleWarp, hwarp] at hrw
    | mma m => simp [roleWarp, hwarp] at hrw
    | cons c => simp [roleWarp, hwarp] at hrw
    | sched s => exact ⟨s, rfl⟩
  have hsite : s.site = .ackWait := ht.sched_ack_wait_site hg hgk hσ0 rfl
  have hσ0' : (code L g).toMachine.after (some (code L g).init) ys =
      some (some (.inr (.sched s))) := by
    unfold Frame.stateAt at hσ0
    rw [hys'] at hσ0
    exact hσ0
  have hσlen : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched s))) := by
    unfold Frame.stateAt
    rw [List.take_length, hys, Machine.after_snoc (code L g).toMachine (some (code L g).init) ys,
      hσ0']
    show (code L g).next (.inr (.sched s)) _ = _
    simp [code, Scheduler.next, hsite]
  have hσp : Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some (.inr (.sched s))) := by
    rw [hlen]
    simpa using hσ0
  have hc : g / L.block = 2 * (g / L.block / 2) := by omega
  obtain ⟨hT, f, hf⟩ := ClcRing.ack_pigeonhole hpre hX ht hg hc hwarp hσp hlast hstate hpar
  have hN : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g) =
      okPolls (clcResp L g) (X.tr g) :=
    ht.sched_ack_count hg (fun k pc' f' => hub g k pc' f') hσlen hsite
  have hgrid := hpre.grid
  have hgb : g / L.block < L.grid := by
    unfold Launch.threads at hg
    have hb0 : 0 < L.block := by rw [hpre.block]; norm_num
    rw [Nat.div_lt_iff_lt_mul hb0]
    exact hg
  have hc2 : 2 * (g / L.block / 2) + 1 < L.grid := by omega
  obtain ⟨b, hb, hbsel, hbc⟩ := ack_candidate hpre hX ht f hc2
  have hcl : g / L.block / 2 = b / L.block / 2 := by
    simp only [ClcRing.consumerSel, decide_eq_true_eq] at hbsel
    have := ClcRing.ctaOf_lt f
    omega
  have hstart : X.tr b ≠ [] :=
    ht.cluster_started hg hgk hσ0 hb (by
      rw [clusterOfCta_eq hpre, clusterOfCta_eq hpre]
      omega)
  have hA : clcAck L b = Bar.loc L (g / L.block) ⟨.clc, 0, false⟩ := by
    unfold clcAck
    congr 1
    omega
  have harrf : arrivals (clcAck L b) (X.tr b) ≤ before.phase := by
    have h1 := ClcRing.ack_arrivals_le hX hbsel
    have h2 : (ClcRing.slot L (g / L.block / 2)).empty 0 = clcAck L b := by
      simp only [ClcRing.slot, clcAck]
      congr 1
      omega
    rw [h2] at h1
    rw [← hA] at hf
    omega
  have hgpoll : ∀ j pc' p' acq' sc',
      (X.tr g)[j]? = some ⟨pc', .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p' true acq' sc'⟩ →
      j + 1 < (X.tr g).length := by
    intro j pc' p' acq' sc' hj
    have hjlt : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
    have hjk : j ≠ ys.length := by
      intro hj'
      subst hj'
      have h1 := hgk
      change (X.tr g)[ys.length]? = _ at h1
      rw [h1] at hj
      have h2 := congrArg (fun e : Event => e.kind) (Option.some.inj hj)
      simp only [Kind.wait.injEq] at h2
      have h3 := congrArg Loc.addr h2.1
      simp [Bar.loc, Bar.off] at h3
    omega
  have harr' : arrivals (clcAck L b) (X.tr b) < okPolls (clcResp L g) (X.tr g) := by
    rw [← hN, ← hT]
    omega
  refine ⟨b, hb, hstart, ⟨f, hbsel⟩, ?_,
    ack_nonexit ht hag hg hb hcl hbsel hbc hσlen hsite hgpoll harr'⟩
  have hE : arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr b) =
      arrivals (clcAck L b) (X.tr b) := by rw [hA]
  rw [hE, ← hT]
  omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
