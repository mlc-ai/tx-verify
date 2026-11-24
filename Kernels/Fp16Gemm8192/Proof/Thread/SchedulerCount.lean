-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery
public import Kernels.Fp16Gemm8192.Proof.Thread.ExitDefs

@[expose] public section

/-! # The scheduler's run invariant

Besides acknowledging responses (`ClcCount`), the scheduler gates its acts on its polls, as views
of `GateRel`: the leader requests the next CTA once per successful poll of its CTA's
acknowledgement barrier (`D.ackView`), and every scheduler arrives on its CTA's response barrier
expecting the next response only after it observed the previous one (`D.respView`). Two more
relations follow its run: the leader's requests exceed its response arrivals by one exactly at
`arriveTx` (`LeadRel`), its requests and reads of responses follow its successful polls
(`StopRel`), its response arrivals are its successful response polls (`ArrRel`), it holds the
response of its latest poll until its exit (`ExitRel`), and it leaves its loop only after a query
naming no first CTA (`ExitQ`). `Run` collects them, and one run invariant proves them all. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

namespace Scheduler

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The acknowledgement barrier as the gate of the leader's requests. -/
def D.ackView (d : D) : GateView :=
  ⟨if d.site = .tryCancel then 1 else 0, 0, if d.site = .elect then 0 else d.ap + 1,
    match d.site with | .exitArrive | .exitWait | .exit => false | _ => true⟩

/-- The response barrier as the gate of the scheduler's own response arrivals. -/
def D.respView (d : D) : GateView :=
  ⟨0, if d.site = .clcWait then 1 else 0, if d.site = .elect then 0 else d.cp,
    match d.site with | .exitArrive | .exitWait | .exit => false | _ => true⟩

/-- The request in flight: from the request to the successful poll of its response. -/
def D.pending (d : D) : Nat := if d.site = .arriveTx ∨ d.site = .clcWait then 1 else 0

/-- The scheduler is still in its task loop: it has not decided to exit. -/
def D.Live (d : D) : Prop := match d.site with
  | .exitArrive | .exitWait | .exit => False
  | .clcStatus | .clcFirst => ∀ rr, d.resp = .clc rr → Loader.claims rr
  | .clcFence | .ack => d.x ≠ Loader.none32
  | _ => True

/-- The event at `i` reads the response buffer, decoding to a response that names a first CTA. -/
def ReadOk (L : Launch) (g : Nat) (es : List Event) (i : Nat) : Prop :=
  ∃ pcr, ∃ src : Acc, ∃ bs rr, es[i]? = some ⟨pcr, .rd src bs⟩ ∧ src.loc = respLoc L g ∧
    src.size = 16 ∧ Flow.responseOf bs = some rr ∧ Loader.claims rr

/-- The scheduler's requests and reads along its run. -/
def StopRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  es.countP (clcIssuesTo (clcResp L g)) ≤ okPolls (clcResp L g) es + d.pending ∧
  (∀ pc p acq sc, es.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
    d.site = .clcLoad) ∧
  (∀ j pc p acq sc, j + 1 < es.length → es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
    d.Live → ReadOk L g es (j + 1))

theorem StopRel.step {d d' : D} {pre : List Event} {e : Event} (h : StopRel L g d pre)
    (hI : (pre ++ [e]).countP (clcIssuesTo (clcResp L g)) ≤
      okPolls (clcResp L g) (pre ++ [e]) + d'.pending)
    (hW : ∀ pc p acq sc, e = ⟨pc, .wait (clcResp L g) p true acq sc⟩ → d'.site = .clcLoad)
    (hnew : ∀ pc p acq sc, pre.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      d'.Live → ReadOk L g (pre ++ [e]) pre.length)
    (hlive : d'.Live → d.Live) : StopRel L g d' (pre ++ [e]) := by
  refine ⟨hI, fun pc p acq sc hl => hW pc p acq sc (by simp at hl; exact hl), ?_⟩
  intro j pc p acq sc hj hw hL
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge (j + 1) pre.length with hlt | hge
  · rw [List.getElem?_append_left (by omega)] at hw
    obtain ⟨pcr, src, bs, rr, hr, h1, h2, h3, h4⟩ := h.2.2 j pc p acq sc hlt hw (hlive hL)
    exact ⟨pcr, src, bs, rr, by rw [List.getElem?_append_left hlt]; exact hr, h1, h2, h3, h4⟩
  · have hj' : j + 1 = pre.length := by omega
    rw [List.getElem?_append_left (by omega)] at hw
    rw [hj']
    refine hnew pc p acq sc ?_ hL
    rw [List.getLast?_eq_getElem?, show pre.length - 1 = j by omega]
    exact hw

theorem counts_snoc (pre : List Event) (e : Event) :
    (pre ++ [e]).countP (clcIssuesTo (clcResp L g)) =
      pre.countP (clcIssuesTo (clcResp L g)) + (if clcIssuesTo (clcResp L g) e then 1 else 0) ∧
    okPolls (clcResp L g) (pre ++ [e]) =
      okPolls (clcResp L g) pre + (if okPoll (clcResp L g) e then 1 else 0) := by
  simp [okPolls, List.countP_append, List.countP_singleton]

/-- The leader's requests and response arrivals along its run: on the leader CTA, the requests
exceed the arrivals by one exactly at `arriveTx`. -/
def LeadRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  Loader.leader L g = true →
    es.countP (clcIssuesTo (clcResp L g)) =
      arrivals (clcResp L g) es + (if d.site = .arriveTx then 1 else 0)

set_option maxHeartbeats 4000000 in
/-- The request at `tryCancel` names the own CTA's response barrier as its mbar. Its response buffer
is 16-byte aligned, so the event is no undefined behaviour. -/
theorem tryCancel_request (hal : L.sharedBase % 1024 = 0)
    (hbase : L.sharedBase + sharedBytes ≤ 2 ^ 18) {t : TState} {pc : Nat} {e : Event}
    {o : Option TState} (hr : t.regs 634 = some (b32 (L.sharedBase + 144)))
    (hm : t.regs 635 = some (b32 (L.sharedBase + 104)))
    (hf : Fires pc (eventTmpl Prod L g t (.clcTryCancel true 634 0 635 0)) e o) :
    ∃ sp tg, e.kind = .clcIssue sp tg ∧ sp.mbar = respBar L g := by
  unfold sharedBytes at hbase
  have hd := effAddr_b32 (L := L) (g := g) hr (by omega)
  have hmb := mbarLoc_b32 (L := L) (g := g) hm (by omega) (by omega)
  have ha16 : (L.sharedBase + 144) % 16 = 0 := by omega
  simp only [eventTmpl, clcTmpl, bind, Except.bind, pure, Except.pure, hd, hmb, ha16,
    ↓reduceIte, ofExec, Fires] at hf
  obtain ⟨hk, -⟩ := hf
  subst hk
  exact ⟨_, _, rfl, by simp [respBar, Bar.loc, Bar.off]⟩

/-- The request the scheduler has open: from its request to the poll of its response. -/
def D.reqOpen (d : D) : Nat :=
  if d.site = .tryCancel ∨ d.site = .arriveTx ∨ d.site = .clcWait then 1 else 0

/-- On the leader CTA, the acknowledgement polls exceed the response polls by the open request:
a leader has one more acknowledgement poll than response polls exactly while its request is open. -/
def AckRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  Lead L g d ∧ (Loader.leader L g = true →
    okPolls (ackBar L g) es = okPolls (clcResp L g) es + d.reqOpen)

/-- A leader's step off the request sites opens no request. -/
theorem reqOpen_next {L : Launch} {g : Nat} (hl : Loader.leader L g = true) {d d' : D} {e : Event}
    (hd : d.site ≠ .ackWait ∧ d.site ≠ .tryCancel ∧ d.site ≠ .arriveTx ∧ d.site ≠ .clcWait)
    (hn : next L g d e = some (some d')) : d'.reqOpen = 0 := by
  obtain ⟨site, ap, cp, resp, x⟩ := d
  obtain ⟨h1, h2, h3, h4⟩ := hd
  simp only at h1 h2 h3 h4 hn
  cases site <;> simp only [next, loopHead, hl, ↓reduceIte] at hn <;> clc_sweep hn <;>
    simp_all [D.reqOpen]

set_option maxHeartbeats 8000000 in
/-- One step of the leader's acknowledgement polls, response polls and open request. -/
theorem ack_step (hpre : Pre P L mem0) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event} (hi : Inv d)
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : AckRel L g d pre) : AckRel L g d' (pre ++ [e]) := by
  obtain ⟨hL, hR⟩ := hq
  refine ⟨next_lead hL hn, fun hl => ?_⟩
  have hq' := hR hl
  have hWa : d.site ≠ .ackWait → okPoll (ackBar L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
      rcases wait_site hpre hi hat hc hf hk with ⟨hs, -⟩ | ⟨-, hm, -⟩
      · exact h1 hs
      · simp [ackBar, respBar, Bar.loc, Bar.off] at hm
  have hWc : d.site ≠ .clcWait → okPoll (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
      rcases wait_site hpre hi hat hc hf hk with ⟨-, hm, -⟩ | ⟨hs, -⟩
      · simp [ackBar, Bar.loc, Bar.off] at hm
      · exact h1 hs
  rw [okPolls_snoc, okPolls_snoc]
  by_cases hA : d.site = .ackWait
  · obtain ⟨ok, acq, sc, he⟩ := ackWait_event hpre hi hA hat hc hf
    subst he
    simp only [next, hA] at hn
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;> subst hn
    · simp [okPoll_wait rfl, ackBar, clcResp, Bar.loc, Bar.off, hA, D.reqOpen] at hq' ⊢
      omega
    · simp [okPoll_wait rfl, ackBar, clcResp, Bar.loc, Bar.off, hA, D.reqOpen] at hq' ⊢
      omega
  by_cases hT : d.site = .tryCancel
  · simp only [next, hT, Option.some.injEq] at hn
    subst hn
    have h1 := hWa hA
    have h2 := hWc (by simp [hT])
    simp [h1, h2, hT, D.reqOpen] at hq' ⊢
    omega
  by_cases hR0 : d.site = .arriveTx
  · simp only [next, hR0, Option.some.injEq] at hn
    subst hn
    have h1 := hWa hA
    have h2 := hWc (by simp [hR0])
    simp [h1, h2, hR0, D.reqOpen] at hq' ⊢
    omega
  by_cases hCW : d.site = .clcWait
  · obtain ⟨ok, acq, sc, he⟩ := clcWait_event hpre hi hCW hat hc hf
    subst he
    simp only [next, hCW] at hn
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;> subst hn
    · simp [okPoll_wait rfl, ackBar, clcResp, respBar, Bar.loc, Bar.off, hCW, D.reqOpen] at hq' ⊢
      omega
    · simp [okPoll_wait rfl, ackBar, clcResp, respBar, Bar.loc, Bar.off, hCW, D.reqOpen] at hq' ⊢
      omega
  have h1 := hWa hA
  have h2 := hWc hCW
  have h3 := reqOpen_next hl ⟨hA, hT, hR0, hCW⟩ hn
  rw [h3]
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  simp [D.reqOpen, hT, hR0, hCW] at hq'
  omega


/-- The scheduler's response arrivals are exactly its successful response polls, plus one at its
response wait: the arrival that opens a wait comes just before it. -/
def ArrRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  arrivals (clcResp L g) es = okPolls (clcResp L g) es + (if d.site = .clcWait then 1 else 0)

/-- A step into the response wait comes from the arrival that opens it, or from the wait itself. -/
theorem next_clcWait {d d' : D} {e : Event} (hn : next L g d e = some (some d'))
    (hd : d'.site = .clcWait) : d.site = .arriveTx ∨ d.site = .clcWait := by
  obtain ⟨site, ap, cp, r, x⟩ := d
  cases site <;> simp only [next, loopHead] at hn
  all_goals (try split at hn)
  all_goals (try split at hn)
  all_goals (try split at hn)
  all_goals (try simp only [Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try obtain ⟨a, -, hn⟩ := hn)
  all_goals (try subst hn)
  all_goals simp_all

/-- One step of the exact response arrivals. -/
theorem arr_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event} (hi : Inv d)
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : ArrRel L g d pre) : ArrRel L g d' (pre ++ [e]) := by
  have hW : d.site ≠ .clcWait → okPoll (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
      rcases wait_site hpre hi hat hc hf hk with ⟨-, hm, -⟩ | ⟨hs, -⟩
      · have := congrArg Loc.addr hm
        simp [ackBar, clcResp, Bar.loc, Bar.off] at this
      · exact h1 hs
  have hA : d.site ≠ .arriveTx → arrivesOn (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨tx, c, rel, sc, hk⟩ := arrivesOn_form h
      rcases arrive_site hpre hg hat hc hf hk with ⟨hs, -⟩ | ⟨-, hm⟩
      · exact h1 hs
      · have := congrArg Loc.addr hm
        simp [clcResp, leadAck, Bar.loc, Bar.off] at this
  unfold ArrRel at hq ⊢
  rw [arrivals_snoc, okPolls_snoc]
  by_cases h1 : d.site = .arriveTx
  · obtain ⟨tx, c, rel, sc, he⟩ := arriveTx_event hpre h1 hat hc hf
    have hAr : arrivesOn (clcResp L g) e = true := by
      rw [arrivesOn_arrive he]
      simp [respBar, clcResp]
    have hPo : okPoll (clcResp L g) e = false := hW (by simp [h1])
    have hd' : d'.site = .clcWait := by
      simp only [next, h1] at hn
      cases hn
      rfl
    simp [hAr, hPo, hd', h1] at hq ⊢
    omega
  by_cases h2 : d.site = .clcWait
  · obtain ⟨ok, acq, sc, he⟩ := clcWait_event hpre hi h2 hat hc hf
    have hAo : arrivesOn (clcResp L g) e = false := hA (by simp [h2])
    cases ok
    · have hPo : okPoll (clcResp L g) e = false := by
        rw [okPoll_wait he]
        simp [respBar, clcResp]
      have hd' : d'.site = .clcWait := by
        simp only [next, h2, he] at hn
        cases hn
        exact h2
      simp [hAo, hPo, hd', h2] at hq ⊢
      omega
    · have hPo : okPoll (clcResp L g) e = true := by
        rw [okPoll_wait he]
        simp [respBar, clcResp]
      have hd' : d'.site = .clcLoad := by
        simp only [next, h2, he] at hn
        cases hn
        rfl
      simp [hAo, hPo, hd', h2] at hq ⊢
      omega
  have hAo : arrivesOn (clcResp L g) e = false := hA h1
  have hPo : okPoll (clcResp L g) e = false := hW h2
  have hd' : d'.site ≠ .clcWait := fun hc' => by
    rcases next_clcWait hn hc' with h | h
    · exact h1 h
    · exact h2 h
  simp [hAo, hPo, hd', h2] at hq ⊢
  omega


/-- The first-CTA word of a response: `Loader.none32` when it names no CTA. -/
def firstX (rr : ClcResponse) : Nat := (rr.firstCta.map fun c => c.1.toNat).getD Loader.none32

/-- The scheduler holds the response `rr`: its successful response poll `j` is followed by the read
of `rr` from its CTA's response buffer. -/
def HeldRead (L : Launch) (g : Nat) (es : List Event) (rr : ClcResponse) : Prop :=
  ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs,
    okPolls (clcResp L g) (es.take j) + 1 = okPolls (clcResp L g) es ∧
    es[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧
    es[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
    src.loc = respLoc L g ∧ src.size = 16 ∧ Flow.responseOf bs = some rr

/-- The scheduler's exit facts along its run: nothing is polled before the election; at its
response load the last event is a successful poll; from the read on it holds the response; in the
acknowledgement and exit stages its word `x` is the held response's; an exit stage that has polled
holds a response with word `none32`. -/
def ExitRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  (d.site = .elect → okPolls (clcResp L g) es = 0) ∧
  (d.site = .clcLoad → ∃ pc p acq sc, es.getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩) ∧
  ((d.site = .clcStatus ∨ d.site = .clcFirst) → ∃ rr, d.resp = .clc rr ∧ HeldRead L g es rr) ∧
  ((d.site = .clcFence ∨ d.site = .ack) → ∃ rr, d.resp = .clc rr ∧ HeldRead L g es rr ∧
    d.x = firstX rr) ∧
  ((d.site = .exitArrive ∨ d.site = .exitWait ∨ d.site = .exit) →
    okPolls (clcResp L g) es = 0 ∨
      ∃ rr, HeldRead L g es rr ∧ d.x = firstX rr ∧ d.x = Loader.none32)

theorem HeldRead.snoc {L : Launch} {g : Nat} {es : List Event} {rr : ClcResponse}
    (h : HeldRead L g es rr) {e : Event} (hw : okPoll (clcResp L g) e = false) :
    HeldRead L g (es ++ [e]) rr := by
  unfold HeldRead at h ⊢
  obtain ⟨j, pc, p, acq, sc, pcr, src, bs, hc, hj, hr, h1, h2, h3⟩ := h
  have hl : j + 1 < es.length := (List.getElem?_eq_some_iff.mp hr).1
  have hcnt := (counts_snoc (L := L) (g := g) es e).2
  rw [hw] at hcnt
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcnt
  refine ⟨j, pc, p, acq, sc, pcr, src, bs, ?_, ?_, ?_, h1, h2, h3⟩
  · rw [hcnt, List.take_append_of_le_length (by omega)]
    exact hc
  · rw [List.getElem?_append_left (by omega)]
    exact hj
  · rw [List.getElem?_append_left hl]
    exact hr

set_option maxHeartbeats 8000000 in
/-- One step of the exit facts. -/
theorem exit_step (hpre : Pre P L mem0) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event} (hi : Inv d)
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : ExitRel L g d pre) : ExitRel L g d' (pre ++ [e]) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hW : d.site ≠ .clcWait → okPoll (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
      rcases wait_site hpre hi hat hc hf hk with ⟨-, hm, -⟩ | ⟨hs, -⟩
      · have := congrArg Loc.addr hm
        simp [ackBar, clcResp, Bar.loc, Bar.off] at this
      · exact h1 hs
  have hcnt := (counts_snoc (L := L) (g := g) pre e).2
  unfold ExitRel at hq ⊢
  obtain ⟨hE, hLd, hSt, hFe, hEx⟩ := hq
  obtain ⟨site, ap, cp, resp, x⟩ := d
  cases site
  case elect =>
    have h0 : okPoll (clcResp L g) e = false := hW (by simp)
    rw [h0] at hcnt
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcnt
    simp only [next] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        refine ⟨by simp [loopHead]; split <;> simp, by simp [loopHead]; split <;> simp,
          by simp [loopHead]; split <;> simp, by simp [loopHead]; split <;> simp,
          by simp [loopHead]; split <;> simp⟩
      · simp only [Option.some.injEq] at hn
        subst hn
        refine ⟨by simp, by simp, by simp, by simp, ?_⟩
        intro _
        left
        rw [hcnt]
        exact hE rfl
    · cases hn
  case ackWait =>
    simp only [next] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        refine ⟨by simp, by simp, by simp, by simp, by simp⟩
      · simp only [Option.some.injEq] at hn
        subst hn
        refine ⟨by simp, by simp, by simp, by simp, by simp⟩
    · cases hn
  case tryCancel =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  case arriveTx =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  case clcWait =>
    obtain ⟨ok, acq, sc, rfl⟩ := clcWait_event hpre hi rfl hat hc hf
    simp only [next] at hn
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact ⟨by simp, by simp, by simp, by simp, by simp⟩
    · simp only [↓reduceIte, Option.some.injEq] at hn
      subst hn
      refine ⟨by simp, ?_, by simp, by simp, by simp⟩
      intro _
      exact ⟨Site.clcWait.pc, cp, acq, sc, by simp [respBar, clcResp]⟩
  case clcLoad =>
    code_at hc
    subst hc
    have hr : t.regs 640 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by sched_values))
    rcases fires_ldAcquire_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · obtain ⟨ha, hs⟩ := (fires_ldAcquire128 (effAddr_b32 hr (by omega)) hat.2.1 hf) a bs hk
      obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp only [next, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      obtain ⟨pc, p, acq, sc, hl⟩ := hLd rfl
      obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
      have hwok : okPoll (clcResp L g) ⟨pc, .wait (clcResp L g) p true acq sc⟩ = true := by
        simp [okPoll, sourceWaitSuccess]
      have hread : okPoll (clcResp L g) ⟨epc, .rd a bs⟩ = false := by
        simp [okPoll, sourceWaitSuccess]
      refine ⟨by simp, by simp, ?_, by simp, by simp⟩
      intro _
      refine ⟨rr, rfl, ?_⟩
      unfold HeldRead
      refine ⟨ys.length, pc, p, acq, sc, epc, a, bs, ?_, ?_, ?_, ha, hs, hrr⟩
      · have htake : (ys ++ [(⟨pc, .wait (clcResp L g) p true acq sc⟩ : Event)] ++
            [(⟨epc, .rd a bs⟩ : Event)]).take ys.length = ys := by simp
        have hcnt2 := (counts_snoc (L := L) (g := g)
          (ys ++ [(⟨pc, .wait (clcResp L g) p true acq sc⟩ : Event)]) ⟨epc, .rd a bs⟩).2
        rw [hread] at hcnt2
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcnt2
        rw [htake, hcnt2]
        have hcnt3 := (counts_snoc (L := L) (g := g) ys
          (⟨pc, .wait (clcResp L g) p true acq sc⟩ : Event)).2
        rw [hwok] at hcnt3
        simp only [↓reduceIte] at hcnt3
        rw [hcnt3]
      · simp
      · simp
    · obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp [next] at hn
  case clcStatus =>
    obtain ⟨rr0, hres0, hH⟩ := hSt (Or.inl rfl)
    simp only [next] at hn
    split at hn
    · rename_i q r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hrr := (query_site hat hc hf hk).2 rr0 hres0
      subst hrr
      have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
      by_cases hfc : r.firstCta.isSome = true
      · simp only [hfc, ite_true]
        refine ⟨by simp, by simp, ?_, by simp, by simp⟩
        intro _
        exact ⟨r, hres0, hH.snoc hq0⟩
      · have hfc' : r.firstCta = none := by simpa using hfc
        simp only [hfc, ite_false, Bool.false_eq_true]
        refine ⟨by simp, by simp, by simp, ?_, by simp⟩
        intro _
        exact ⟨r, hres0, hH.snoc hq0, by simp [firstX, hfc']⟩
    · cases hn
  case clcFirst =>
    obtain ⟨rr0, hres0, hH⟩ := hSt (Or.inr rfl)
    simp only [next] at hn
    split at hn
    · rename_i q r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hrr := (query_site hat hc hf hk).2 rr0 hres0
      subst hrr
      have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
      refine ⟨by simp, by simp, by simp, ?_, by simp⟩
      intro _
      exact ⟨r, hres0, hH.snoc hq0, rfl⟩
    · cases hn
  case clcFence =>
    obtain ⟨rr0, hres0, hH, hx⟩ := hFe (Or.inl rfl)
    simp only [next, Option.some.injEq] at hn
    subst hn
    have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
    exact ⟨by simp, by simp, by simp, fun _ => ⟨rr0, hres0, hH.snoc hq0, hx⟩, by simp⟩
  case ack =>
    obtain ⟨rr0, hres0, hH, hx⟩ := hFe (Or.inr rfl)
    have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
    simp only [next] at hn
    split at hn
    · rename_i hxn
      simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      intro _
      exact Or.inr ⟨rr0, hH.snoc hq0, hx, hxn⟩
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨by simp [loopHead]; split <;> simp, by simp [loopHead]; split <;> simp,
        by simp [loopHead]; split <;> simp, by simp [loopHead]; split <;> simp,
        by simp [loopHead]; split <;> simp⟩
  case exitArrive =>
    have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
    simp only [next, Option.some.injEq] at hn
    subst hn
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro _
    rcases hEx (Or.inl rfl) with h | ⟨rr, hH, hx, hn0⟩
    · left
      rw [hcnt, h, hq0]
      simp
    · exact Or.inr ⟨rr, hH.snoc hq0, hx, hn0⟩
  case exitWait =>
    have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
    simp only [next, Option.some.injEq] at hn
    subst hn
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro _
    rcases hEx (Or.inr (Or.inl rfl)) with h | ⟨rr, hH, hx, hn0⟩
    · left
      rw [hcnt, h, hq0]
      simp
    · exact Or.inr ⟨rr, hH.snoc hq0, hx, hn0⟩
  case exit =>
    simp [next] at hn

/-- One scheduler step keeps the exit-stage facts. -/
theorem exitQ_step {s s' : D} {es : List Event} {e : Event} (h : ExitQ L g s es)
    (hn : next L g s e = some (some s')) : ExitQ L g s' (es ++ [e]) := by
  obtain ⟨hA, hB⟩ := h
  obtain ⟨site, ap, cp, resp, x⟩ := s
  obtain ⟨pc, kind⟩ := e
  simp only [ExitQ] at hA hB ⊢
  cases site <;> simp only [next, loopHead] at hn
  · -- elect: a lane that is not the elected one leaves for the exit stage at once
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i a b c
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨fun hs => by simp only at hs; split_ifs at hs <;> simp at hs,
        fun hs => by simp only at hs; split_ifs at hs <;> simp at hs⟩
    · rename_i hne
      simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨fun _ => Or.inr ⟨es.length, ⟨pc, .elect a b c⟩, by simp, a, b, c, rfl,
        fun heq => hne heq.symm⟩, fun hs => by simp at hs⟩
  · -- ackWait
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i w p' ok acq sc
    split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;> simp
  · -- tryCancel
    simp only [Option.some.injEq] at hn
    subst hn
    simp
  · -- arriveTx
    simp only [Option.some.injEq] at hn
    subst hn
    simp
  · -- clcWait
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i w p' ok acq sc
    split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;> simp
  · -- clcLoad
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i w bs
    cases hr : Flow.responseOf bs <;> simp only [hr, Option.map_none, Option.map_some,
      Option.some.injEq, reduceCtorEq] at hn
    subst hn
    simp
  · -- clcStatus: the query decides between the first-CTA query and the fence
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i q r
    by_cases hf : r.firstCta.isSome = true
    · simp only [hf, ite_true, Option.some.injEq] at hn
      subst hn
      simp
    · have hf' : r.firstCta.isSome = false := by simpa using hf
      have hnone : r.firstCta = none := by simpa using hf'
      simp only [hf', Bool.false_eq_true, ite_false, Option.some.injEq] at hn
      subst hn
      refine ⟨fun hs => by simp at hs, fun _ hx => noClaimQ_snoc rfl ?_⟩
      simp [Loader.claims, hnone]
  · -- clcFirst: the second query names the first CTA
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i q r
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun hs => by simp at hs, fun _ hx => noClaimQ_snoc rfl ?_⟩
    simp only [Loader.claims, ne_eq, not_not]
    exact hx
  · -- clcFence: the acknowledgement keeps the fence's value
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun hs => by simp at hs, fun _ hx => ?_⟩
    exact NoClaimQ.append ⟨pc, kind⟩ (hB (Or.inl rfl) hx)
  · -- ack: the no-CTA value leads to the exit stage, otherwise back to the loop
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨fun _ => Or.inl (NoClaimQ.append _ ?_), fun hs => by simp at hs⟩
      exact hB (Or.inr rfl) ‹_›
    · simp only [Option.some.injEq] at hn
      subst hn
      refine ⟨fun hs => by simp only at hs; split_ifs at hs <;> simp at hs,
        fun hs => by simp only at hs; split_ifs at hs <;> simp at hs⟩
  · -- exitArrive
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun _ => ?_, fun hs => by simp at hs⟩
    rcases hA (Or.inl rfl) with h1 | h1
    · exact Or.inl (NoClaimQ.append _ h1)
    · exact Or.inr (ElectOut.append _ h1)
  · -- exitWait
    simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨fun _ => ?_, fun hs => by simp at hs⟩
    rcases hA (Or.inr (Or.inl rfl)) with h1 | h1
    · exact Or.inl (NoClaimQ.append _ h1)
    · exact Or.inr (ElectOut.append _ h1)
  · -- exit: no further step
    simp at hn

/-- The scheduler's run facts at its state `d` after the events `es`. -/
structure Run (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop where
  ackGate : GateRel (ackBar L g) (clcIssuesTo (clcResp L g)) d.ackView es
  respGate : GateRel (clcResp L g) (arrivesOn (clcResp L g)) d.respView es
  lead : LeadRel L g d es
  stop : StopRel L g d es
  ack : AckRel L g d es
  arr : ArrRel L g d es
  exit : ExitRel L g d es
  exitQ : ExitQ L g d es

/-- The scheduler's run facts along a thread's run. The prologue is quiet, and the other roles are
not constrained. -/
def SchedInv (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, es => Quiet es
  | .inr (.sched s), es => Run L g s es
  | _, _ => True

set_option maxHeartbeats 8000000 in
theorem sched_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    GateStep (ackBar L g) (clcIssuesTo (clcResp L g)) d.ackView e d'.ackView ∧
      GateStep (clcResp L g) (arrivesOn (clcResp L g)) d.respView e d'.respView := by
  have hW : ∀ m, d.site ≠ .ackWait → d.site ≠ .clcWait → okPoll m e = false := fun m h1 h2 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
      rcases wait_site hpre hi hat hc hf hk with ⟨hs, -⟩ | ⟨hs, -⟩ <;> contradiction
  have hA : d.site ≠ .arriveTx → arrivesOn (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨tx, c, rel, sc, hk⟩ := arrivesOn_form h
      rcases arrive_site hpre hg hat hc hf hk with ⟨hs, -⟩ | ⟨-, hm⟩
      · contradiction
      · have := congrArg Loc.addr hm
        simp [clcResp, leadAck, Bar.loc, Bar.off] at this
  have hI : ∀ m, d.site ≠ .tryCancel → clcIssuesTo m e = false := fun m h1 =>
    Bool.eq_false_iff.mpr fun h => h1 (by
      unfold clcIssuesTo at h
      split at h
      · exact clcIssue_site hat hc hf ‹_›
      · cases h)
  have hA' := hA
  have hI' := hI (clcResp L g)
  obtain ⟨site, ap, cp, r, x⟩ := d
  have hap : ap < 2 := hi.ap
  have hcp : cp < 2 := hi.cp
  cases site
  case ackWait =>
    obtain ⟨ok, acq, sc, rfl⟩ := ackWait_event hpre hi rfl hat hc hf
    simp only [next] at hn
    cases ok <;> simp only [Option.some.injEq, ↓reduceIte, Bool.false_eq_true] at hn <;>
      subst hn <;> simp [GateStep, D.ackView, D.respView, clcIssuesTo, arrivesOn,
        sourceArrive, okPoll, sourceWaitSuccess, ackBar, clcResp, Bar.loc, Bar.off]
    omega
  case clcWait =>
    obtain ⟨ok, acq, sc, rfl⟩ := clcWait_event hpre hi rfl hat hc hf
    simp only [next] at hn
    cases ok <;> simp only [Option.some.injEq, ↓reduceIte, Bool.false_eq_true] at hn <;>
      subst hn <;> simp [GateStep, D.ackView, D.respView, clcIssuesTo, arrivesOn,
        sourceArrive, okPoll, sourceWaitSuccess, ackBar, clcResp, respBar, Bar.loc, Bar.off]
    omega
  all_goals have hok1 := hW (ackBar L g) (by simp) (by simp)
  all_goals have hok2 := hW (clcResp L g) (by simp) (by simp)
  all_goals clear hW hA hI hat hc hf
  all_goals dsimp only at hA' hI'
  all_goals simp only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false, forall_const,
    IsEmpty.forall_iff] at hA' hI'
  all_goals simp only [next, loopHead] at hn
  clc_sweep hn
  all_goals (simp only [GateStep, D.ackView, D.respView, hok1, hok2]; split_ifs <;> simp_all)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- One step of the leader's requests and response arrivals. -/
theorem lead_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event}
    (hat : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : LeadRel L g d pre) : LeadRel L g d' (pre ++ [e]) := by
  unfold LeadRel at hq ⊢
  intro hl
  have hq' := hq hl
  have hI : d.site ≠ .tryCancel → clcIssuesTo (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => h1 (by
      unfold clcIssuesTo at h
      split at h
      · exact clcIssue_site hat hc hf ‹_›
      · cases h)
  have hA : d.site ≠ .arriveTx → arrivesOn (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨tx, c, rel, sc, hk⟩ := arrivesOn_form h
      rcases arrive_site hpre hg hat hc hf hk with ⟨hs, -⟩ | ⟨-, hm⟩
      · exact h1 hs
      · have := congrArg Loc.addr hm
        simp [clcResp, leadAck, Bar.loc, Bar.off] at this
  simp only [arrivals, List.countP_append, List.countP_singleton] at hq' ⊢
  obtain ⟨site, ap, cp, resp, x⟩ := d
  cases site
  case tryCancel =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcIssue_0)
    have h4 := hat.2.2.2.2
    have hr : t.regs 634 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem h4 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
    have hm : t.regs 635 = some (b32 (L.sharedBase + 104)) :=
      (holds_mem h4 (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by sched_values))
    obtain ⟨sp, tg, hk, hmb⟩ :=
      tryCancel_request hpre.sharedAlignment hpre.sharedRange hr hm hf
    have hcl : clcIssuesTo (clcResp L g) e = true := by simp [clcIssuesTo, hk, hmb]
    have hna : arrivesOn (clcResp L g) e = false :=
      arrivesOn_notArrive (fun l tx c rel sc => by simp [hk])
    simp only [hcl, hna, ↓reduceIte, Bool.false_eq_true, Nat.add_zero, reduceCtorEq] at hq' ⊢
    omega
  case arriveTx =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    obtain ⟨tx, c, rel, sc, he⟩ := arriveTx_event hpre rfl hat hc hf
    have hna : clcIssuesTo (clcResp L g) e = false := by simp [clcIssuesTo, he]
    have hyes : arrivesOn (clcResp L g) e = true := by
      rw [arrivesOn_arrive he]
      simp [respBar, clcResp]
    simp only [hna, hyes, ↓reduceIte, Bool.false_eq_true, Nat.add_zero, reduceCtorEq] at hq' ⊢
    omega
  all_goals have h1 := hI (by simp)
  all_goals have h2 := hA (by simp)
  all_goals clear hI hA
  all_goals simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hq' ⊢
  all_goals try simp only [next, loopHead, hl, ↓reduceIte] at hn
  clc_sweep hn
  all_goals simp_all

set_option maxHeartbeats 8000000 in
theorem stop_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hi : Inv d) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : StopRel L g d pre) : StopRel L g d' (pre ++ [e]) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hW : d.site ≠ .clcWait → okPoll (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
      rcases wait_site hpre hi hat hc hf hk with ⟨-, hm, -⟩ | ⟨hs, -⟩
      · have := congrArg Loc.addr hm
        simp [clcResp, ackBar, Bar.loc, Bar.off] at this
      · exact h1 hs
  have hI : d.site ≠ .tryCancel → clcIssuesTo (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => h1 (by
      unfold clcIssuesTo at h
      split at h
      · exact clcIssue_site hat hc hf ‹_›
      · cases h)
  have hWk : d.site ≠ .clcWait → ∀ pc p acq sc, e ≠ ⟨pc, .wait (clcResp L g) p true acq sc⟩ :=
    fun h1 pc p acq sc he => by
      have := hW h1
      rw [okPoll_wait he] at this
      simp at this
  have hold : d.site ≠ .clcLoad → ∀ pc p acq sc,
      pre.getLast? ≠ some ⟨pc, .wait (clcResp L g) p true acq sc⟩ :=
    fun h1 pc p acq sc hl => h1 (hq.2.1 pc p acq sc hl)
  obtain ⟨hc1, hc2⟩ := counts_snoc (L := L) (g := g) pre e
  have hI0 := hq.1
  obtain ⟨site, ap, cp, resp, x⟩ := d
  cases site
  case clcWait =>
    obtain ⟨ok, acq, sc, rfl⟩ := clcWait_event hpre hi rfl hat hc hf
    have hok := okPoll_wait (m := clcResp L g) (rfl : (⟨Site.clcWait.pc, .wait (respBar L g) cp ok
      acq sc⟩ : Event) = _)
    have hiss := hI (by simp)
    simp only [next] at hn
    cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;> subst hn
    · refine hq.step ?_ (fun _ _ _ _ h => by cases h) (fun _ _ _ _ hl =>
      absurd hl (hold (by simp) _ _ _ _))
        id
      simp only [hok, hiss, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1 hc2
      rw [hc1, hc2]
      exact hI0
    · refine hq.step ?_ (fun _ _ _ _ _ => rfl)
        (fun _ _ _ _ hl => absurd hl (hold (by simp) _ _ _ _)) (fun _ => trivial)
      simp only [hok, hiss, Bool.true_and, decide_true, ↓reduceIte, Bool.false_eq_true,
        Nat.add_zero] at hc1 hc2
      rw [hc1, hc2]
      simp [D.pending] at hI0 ⊢
      omega
  case clcLoad =>
    code_at hc
    subst hc
    have hr : t.regs 640 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by sched_values))
    rcases fires_ldAcquire_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · obtain ⟨ha, hs⟩ := (fires_ldAcquire128 (effAddr_b32 hr (by omega)) hat.2.1 hf) a bs hk
      obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp only [next, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      refine hq.step ?_ (fun _ _ _ _ h => by cases h) ?_ (fun _ => trivial)
      · have h1 := hI (by simp)
        have h2 := hW (by simp)
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1 hc2
        rw [hc1, hc2]
        exact hI0
      · intro _ _ _ _ _ hL
        exact ⟨epc, a, bs, rr, by simp, ha, hs, hrr, hL rr rfl⟩
    · obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp [next] at hn
  case tryCancel =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    have h2 := hW (by simp)
    refine hq.step ?_ (fun _ _ _ _ h => absurd h (hWk (by simp) _ _ _ _))
      (fun _ _ _ _ hl => absurd hl (hold (by simp) _ _ _ _)) (fun _ => trivial)
    rw [hc1, hc2]
    simp only [h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    simp [D.pending] at hI0 ⊢
    split <;> omega
  case clcFirst =>
    simp only [next] at hn
    split at hn
    · rename_i q r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hrr := (query_site hat hc hf hk).2
      have h1 := hI (by simp)
      have h2 := hW (by simp)
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1 hc2
      refine hq.step (by rw [hc1, hc2]; exact hI0) (fun _ _ _ _ h =>
        absurd h (hWk (by simp) _ _ _ _))
        (fun _ _ _ _ hl => absurd hl (hold (by simp) _ _ _ _)) ?_
      intro hL rr' hr'
      simp only at hr'
      rw [← hrr rr' hr']
      exact hL
    · cases hn
  all_goals have h1 := hI (by simp)
  all_goals have h2 := hW (by simp)
  all_goals have h3 := hWk (by simp)
  all_goals have h4 := hold (by simp)
  all_goals clear hW hI hWk hold hat hc hf
  all_goals simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1 hc2
  all_goals simp only [next, loopHead] at hn
  clc_sweep hn
  all_goals refine hq.step ?_ (fun _ _ _ _ h => absurd h (h3 _ _ _ _))
                (fun _ _ _ _ hl => absurd hl (h4 _ _ _ _)) ?_
  all_goals first
    | (rw [hc1, hc2]; simp [D.pending] at hI0 ⊢; omega)
    | simp_all [D.Live]

/-- Along a thread's run, its scheduler's run facts satisfy `SchedInv`. -/
theorem schedInv (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      SchedInv L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (SchedInv L g) quiet_nil ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · have hq' := hq.snoc (Prologue.fires_quiet hc hf)
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | (l' | m' | sd' | cs')
    · exact hq'
    all_goals try trivial
    obtain rfl := Prologue.next_sched hn
    have hA := hq' (ackBar L g)
    have hR := hq' (clcResp L g)
    have hnone : ∀ (j pc p : Nat) (acq : Bool) (sc : MbarScope),
        (pre ++ [e])[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ → False := by
      intro j pc p acq sc hj
      have hmem := List.mem_of_getElem? hj
      have : 0 < okPolls (clcResp L g) (pre ++ [e]) :=
        List.countP_pos_iff.mpr ⟨_, hmem, by simp [okPoll, sourceWaitSuccess]⟩
      omega
    refine ⟨GateRel.start hR.2.2.2.2 hA.1 (by simp [D.ackView, Prologue.schedStart])
        (by simp [D.ackView, Prologue.schedStart]),
      GateRel.start hR.2.1 hR.1 rfl (by simp [D.respView, Prologue.schedStart]),
      fun _ => by simp [Prologue.schedStart, hR.2.1, hR.2.2.2.2],
      ⟨(by rw [hR.2.2.2.2, hR.1]; omega), fun pc p acq sc hl => ?_,
        fun j pc p acq sc _ hj => (hnone j pc p acq sc hj).elim⟩,
      ⟨fun h => by simp [Prologue.schedStart] at h,
        fun _ => by rw [hA.1, hR.1]; simp [D.reqOpen, Prologue.schedStart]⟩,
      by unfold ArrRel; rw [hR.2.1, hR.1]; simp [Prologue.schedStart],
      ⟨fun _ => hR.1, fun h => by simp [Prologue.schedStart] at h,
        fun h => by simp [Prologue.schedStart] at h, fun h => by simp [Prologue.schedStart] at h,
        fun h => by simp [Prologue.schedStart] at h⟩,
      by simp [ExitQ, Prologue.schedStart]⟩
    rw [List.getLast?_eq_getElem?] at hl
    exact (hnone _ pc p acq sc hl).elim
  · obtain ⟨l', -, rfl⟩ := next_of_loader hn; trivial
  · obtain ⟨m', -, rfl⟩ := next_of_mma hn; trivial
  · obtain ⟨s', hs, rfl⟩ := next_of_sched hn
    have hq : Run L g sd pre := hq
    obtain ⟨h1, h2⟩ := sched_step hpre hg hinv.1 hat hc hf hs
    exact (⟨GateRel.step hq.ackGate h1, GateRel.step hq.respGate h2,
      lead_step hpre hg hat hc hf hs hq.lead, stop_step hpre hinv.1 hat hc hf hs hq.stop,
      ack_step hpre hinv.1 hat hc hf hs hq.ack, arr_step hpre hg hinv.1 hat hc hf hs hq.arr,
      exit_step hpre hinv.1 hat hc hf hs hq.exit, exitQ_step hq.exitQ hs⟩ : Run L g s' _)
  · obtain ⟨c', -, rfl⟩ := next_of_cons hn; trivial

/-- The scheduler's run facts at a state of its run. -/
theorem run_of {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {s : D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.sched s)))) : Run L g s ((X.tr g).take k) :=
  schedInv hpre hg (Frame.trace (fun _ => sound hpre) hX hg) k _ hσ

/-- The scheduler's run facts at the end of its trace. -/
theorem run_end {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {s : D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s)))) : Run L g s (X.tr g) := by
  have h := run_of hpre hX hg (k := (X.tr g).length) (by rw [List.take_length]; exact hσ)
  rwa [List.take_length] at h

/-- The scheduler's state and site at one of its events. -/
private theorem at_event {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) {s : D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.sched s)))) :
    ∃ t ins o, Inv s ∧ At t s.site.pc (facts L g s) ∧ kernel.code[s.site.pc]? = some ins ∧
      Fires s.site.pc (eventTmpl Prod L g t ins.op) e o ∧ Run L g s ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  exact ⟨t, ins, o, hinv.1, hat, hc, hfire, run_of hpre hX hg hσ⟩

end Scheduler

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The leader's acknowledgement poll uses the parity after its successful polls. -/
theorem Scheduler.ack_poll_parity (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.sched s))))
    {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) p ok acq sc) :
    p % 2 = (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) ((X.tr g).take k) + 1) % 2 := by
  obtain ⟨t, ins, o, hi, hat, hc, hf, hr⟩ := Scheduler.at_event hpre hX hg he hσ
  have h := hr.ackGate
  rcases Scheduler.wait_site hpre hi hat hc hf hk with ⟨hs, -, rfl⟩ | ⟨-, hm, -⟩
  · have := h.2 (by simp [Scheduler.D.ackView, hs])
    simp only [Scheduler.D.ackView, hs, reduceCtorEq, ↓reduceIte, Scheduler.ackBar] at this
    have := hi.ap
    omega
  · have := congrArg Loc.addr hm
    simp [Scheduler.respBar, Bar.loc, Bar.off] at this

/-- A response arrival follows the scheduler's observation of every earlier response. -/
theorem Scheduler.response_budget (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.sched s))))
    {tx n : Nat} {rel : Bool} {sc : MbarScope}
    (hk : e.kind = .arrive (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) tx n rel sc) :
    arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) := by
  obtain ⟨t, ins, o, hi, hat, hc, hf, hr⟩ := Scheduler.at_event hpre hX hg he hσ
  rcases Scheduler.arrive_site hpre hg hat hc hf hk with ⟨hs, -⟩ | ⟨-, hm⟩
  · have := hr.respGate.1
    simp only [Scheduler.D.respView, hs, reduceCtorEq, ↓reduceIte] at this
    exact this
  · have := congrArg Loc.addr hm
    simp [Scheduler.leadAck, Bar.loc, Bar.off] at this

/-- A request follows more successful acknowledgement polls than earlier requests. -/
theorem Scheduler.cancel_budget (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.sched s))))
    {sp : Clc.Spec} {tg : List Nat} (hk : e.kind = .clcIssue sp tg)
    (hm : sp.mbar = Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) :
    ((X.tr g).take k).countP (clcIssuesTo sp.mbar) + 1 ≤
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) ((X.tr g).take k) := by
  obtain ⟨t, ins, o, hi, hat, hc, hf, hr⟩ := Scheduler.at_event hpre hX hg he hσ
  have h := hr.ackGate
  have hs := Scheduler.clcIssue_site hat hc hf hk
  rw [hm]
  exact GateRel.budget h (by simp [Scheduler.D.ackView, hs]) rfl

/-- A leader scheduler at its acknowledgement poll has polled its acknowledgement barrier as often
as
its response barrier: each earlier request was answered by one successful response poll and one
acknowledgement poll. -/
theorem Scheduler.sched_ack_count (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s))))
    (hs : s.site = .ackWait) :
    okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g) =
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  obtain ⟨hL, hR⟩ := (Scheduler.run_end hpre hX hg hσ).ack
  have h2 := hR (hL (Or.inl hs))
  rw [h2]
  simp [D.reqOpen, hs]

/-- At a scheduler's response wait it has arrived on its CTA's response barrier once more than it
has
polled that barrier successfully (`sched_arrive_clc`). -/
theorem Scheduler.sched_arrive (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s)))) (hs : s.site = .clcWait) :
    arrivals (clcResp L g) (X.tr g) = okPolls (clcResp L g) (X.tr g) + 1 := by
  have h2 := (Scheduler.run_end hpre hX hg hσ).arr
  unfold Scheduler.ArrRel at h2
  rw [h2, hs]
  simp

/-- At a request, the scheduler has requested at most once per observed response, and each of
its earlier successful response polls was followed by a read of a response that claims a CTA. -/
theorem Scheduler.sched_issue (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {e : Event} (he : X.get (g, k) = some e) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.sched s))))
    {sp : Clc.Spec} {tg : List Nat} (hk : e.kind = .clcIssue sp tg) :
    ((X.tr g).take k).countP (clcIssuesTo (clcResp L g)) ≤ okPolls (clcResp L g) ((X.tr g).take k) ∧
    ∀ j pc p acq sc, j < k → X.get (g, j) = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      ∃ pcr, ∃ src : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ ∧
        src.loc = respLoc L g ∧ src.size = 16 ∧ Flow.responseOf bs = some rr ∧
        Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hs := Scheduler.clcIssue_site hat hc hfire hk
  have h := (Scheduler.run_of hpre hX hg hσ).stop
  have hk' : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  refine ⟨by simpa [Scheduler.D.pending, hs] using h.1, fun j pc p acq sc hj hw => ?_⟩
  have hw' : ((X.tr g).take k)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := by
    rw [List.getElem?_take_of_lt hj]; exact hw
  have hj1 : j + 1 < k := by
    by_contra hn
    have hl : ((X.tr g).take k).getLast? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := by
      rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hk',
        show k - 1 = j by omega]
      exact hw'
    have := h.2.1 _ _ _ _ hl
    rw [hs] at this
    cases this
  obtain ⟨pcr, src, bs, rr, hr, h1, h2, h3, h4⟩ :=
    h.2.2 j pc p acq sc (by simp only [List.length_take, Nat.min_eq_left hk']; omega) hw'
      (by simp [Scheduler.D.Live, hs])
  rw [List.getElem?_take_of_lt hj1] at hr
  exact ⟨pcr, src, bs, rr, hr, h1, h2, h3, h4⟩

/-- **The scheduler's exit holds the response that claims no CTA.** A scheduler in its exit stage
that has polled successfully holds, after its last successful response poll, a read of a response
that claims no CTA. -/
theorem Scheduler.sched_exit (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s))))
    (hs : s.site = .exitArrive ∨ s.site = .exitWait ∨ s.site = .exit)
    (hk : 0 < okPolls (clcResp L g) (X.tr g)) :
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
      okPolls (clcResp L g) ((X.tr g).take j) + 1 = okPolls (clcResp L g) (X.tr g) ∧
      (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ ∧
      (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
      src.loc = respLoc L g ∧ src.size = 16 ∧ Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr :=
        by
  obtain ⟨-, -, -, -, h5⟩ := (Scheduler.run_end hpre hX hg hσ).exit
  rcases h5 hs with h0 | ⟨rr, hH, hx, hn⟩
  · omega
  · obtain ⟨j, pc, p, acq, sc, pcr, src, bs, h1, h2', h3, h4, h5', h6⟩ := hH
    refine ⟨j, pc, p, acq, sc, pcr, src, bs, rr, h1, h2', h3, h4, h5', h6, ?_⟩
    have hf : Scheduler.firstX rr = Loader.none32 := hx.symm.trans hn
    unfold Scheduler.firstX at hf
    exact fun hc => hc hf

/-- **A scheduler at its response wait has read no non-claiming response after a successful
response poll**: a read of a response after a successful poll claims a CTA while the scheduler waits
for its next response (`StopRel`, the scheduler being live there). -/
theorem Scheduler.sched_fail_wait (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {s : Scheduler.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.sched s))))
    (hs : s.site = .clcWait) :
    ∀ j pc p acq sc pcr src bs rr, (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ →
      (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ → src.loc = respLoc L g → src.size = 16 →
      Flow.responseOf bs = some rr → Loader.claims rr := by
  intro j pc p acq sc pcr src bs rr ha hb _ _ hr
  obtain ⟨pcr', src', bs', rr', hb', -, -, hr', hc⟩ := (Scheduler.run_end hpre hX hg hσ).stop.2.2 j
    pc p acq sc (List.getElem?_eq_some_iff.mp hb).1 ha (by simp [Scheduler.D.Live, hs])
  rw [hb] at hb'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hb'
  obtain ⟨-, -, rfl⟩ := hb'
  rw [hr] at hr'
  cases hr'
  exact hc

end
end PTX.Kernels.Fp16Gemm8192.Proof
