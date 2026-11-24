-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsStoreGeometry
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.NthEv
public import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
public import Lemmas.Flow.ContinuingEvent
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

private inductive CreditGate where
  | entry
  | terminal
  | publication (round : Thread.Scores.Round)

private def creditPoll : CreditGate → Fin 10
  | .entry => 0
  | .terminal => 9
  | .publication .first => 3
  | .publication .biased => 6
  | .publication .plain => 8
  | .publication .final => 9

private def publicationPc : Thread.Scores.Round → Nat
  | .first => 4397
  | .biased => 5683
  | .plain => 6891
  | .final => 7616

private def creditStart : CreditGate → Nat
  | .entry => 3103
  | .terminal => 3103
  | .publication round => publicationPc round + 1

private def creditEnd (gate : CreditGate) : Nat := (waitSite (creditPoll gate)).pc

private abbrev creditRange (gate : CreditGate) (pc : Nat) : Prop :=
  creditStart gate ≤ pc ∧ pc ≤ creditEnd gate

private def creditEscape : CreditGate → Nat → Prop
  | .entry, pc => 7733 ≤ pc
  | .terminal, _ => False
  | .publication _, _ => False

private instance (gate : CreditGate) (pc : Nat) : Decidable (creditEscape gate pc) := by
  cases gate <;> unfold creditEscape <;> infer_instance

private def creditRangeCode (gate : CreditGate) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (creditRange gate dst ∨ creditEscape gate dst)
  | .brx .. => false
  | _ => true

private theorem creditRangeCodeAt (gate : CreditGate) {pc : Nat} {ins : Instr}
    (hLo : creditStart gate ≤ pc) (hHi : pc < creditEnd gate)
    (hCode : kernel.code[pc]? = some ins) : creditRangeCode gate ins.op = true := by
  let lo := creditStart gate
  let len := creditEnd gate - lo
  have hAll : ((kernel.code.drop lo).take len).all (fun ins => creditRangeCode gate ins.op) =
      true := by
    cases gate <;> (try cases ‹Thread.Scores.Round›) <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll ins
  apply List.mem_of_getElem? (i := pc-lo)
  rw [List.getElem?_take_of_lt (by dsimp [len, lo]; omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hCode]

private theorem creditRangesSegments (gate : CreditGate) :
    Assumptions.swExp2Sites.all (fun pc =>
      !decide (creditRange gate pc) || match cuteExp2.matchAt kernel pc with
        | none => false
        | some m => decide (creditRange gate m.stop)) = true := by
  cases gate <;> (try cases ‹Thread.Scores.Round›) <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem ordinaryEvents :
    kernel.code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true := by
  decide +kernel

private theorem withinCreditRange (gate : CreditGate)
    {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hs : creditRange gate s.pc) (hLt : s.pc < creditEnd gate)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    creditRange gate u.pc ∨ creditEscape gate u.pc := by
  rcases hs with ⟨hLo, hHi⟩
  have next : creditRange gate (s.pc+1) := ⟨by omega, by omega⟩
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
    have hCode := creditRangeCodeAt gate hLo hLt hc
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · exact .inl next
    · rcases scoreExecLocal hLocal with hFrame | ⟨m, hSite, hm, hRun⟩
      · have hPc := hFrame.pc
        cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
        case bra dst uni =>
          rw [hPc]
          simpa [ho, creditRangeCode] using hCode
        case brx => simp [ho, creditRangeCode] at hCode
        all_goals exact .inl (hPc ▸ next)
      · have hStop := List.all_eq_true.mp (creditRangesSegments gate) _ hSite
        rw [hm] at hStop
        have hsNow : creditRange gate s.pc := ⟨hLo, hHi⟩
        rw [decide_eq_true hsNow, Bool.not_true, Bool.false_or] at hStop
        rw [(scoreSegmentFrame hRun).1]
        exact .inl (of_decide_eq_true hStop)
  · obtain ⟨ins, hc, hLocal, hFire⟩ := estep_event_source he
    have hOp := List.all_eq_true.mp ordinaryEvents _ (List.mem_of_getElem? hc)
    have hFrame := Epilogue.ordinaryEventFrame
      (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hLocal, Bool.false_or] using hOp)
    rcases callbackFrame_fires hFrame hFire with h | h
    · exact .inl (h ▸ ⟨hLo, hHi⟩)
    · exact .inl (h ▸ next)

private theorem noLaterPublicationInCreditRange (round : Thread.Scores.Round) {pc : Nat}
    (hLo : creditStart (.publication round) ≤ pc) (hHi : pc ≤ creditEnd (.publication round) + 2) :
    pc ∉ softmaxStatsSites := by
  cases round <;>
    simp [creditStart, publicationPc, creditEnd, creditPoll, waitSite, softmaxStatsSites] at * <;>
    omega

private theorem remainsEscaped {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 7733 ≤ s.pc) (hStep : WStep kernel Assumptions.all l g s ev u) : 7733 ≤ u.pc := by
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
    · change 7733 ≤ s.pc+1
      omega
    · rcases scoreExecLocal hExec with hF | ⟨m, hm, _, _⟩
      · let checks (i : Instr) := match i.op with
          | .bra dst _ => decide (7733 ≤ dst)
          | .brx .. => false
          | _ => true
        have hStatic : (kernel.code.drop 7733).all checks = true := by
          set_option maxRecDepth 100000 in kernel_rfl
        have hc' : (kernel.code.drop 7733)[s.pc-7733]? = some ins := by
          rw [List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
        have hA := List.all_eq_true.mp hStatic ins (List.mem_of_getElem? hc')
        have hPc := hF.pc
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
        case bra dst uni =>
          rw [hPc]
          simpa only [checks, hop, decide_eq_true_eq] using hA
        case brx => simp [checks, hop] at hA
        all_goals omega
      · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hm
        omega
  · obtain ⟨ins, hc, hl, hFire⟩ := estep_event_source he
    have hOp := List.all_eq_true.mp ordinaryEvents _ (List.mem_of_getElem? hc)
    have hFrame := Epilogue.ordinaryEventFrame
      (A := Assumptions.all) (l := l) (g := g) (s := s)
      (by simpa only [hl, Bool.false_or] using hOp)
    rcases callbackFrame_fires hFrame hFire with h | h <;> omega

private def successCredit (gate : CreditGate) (e : Event) : Prop :=
  e.pc = creditEnd gate ∧ ∃ loc parity acq scope, e.kind = .wait loc parity true acq scope

private def beforeCredit (gate : CreditGate) (s : TState) : Prop :=
  creditRange gate s.pc ∨
  s.pc = creditEnd gate + 1 ∧ s.fault = none ∧
    s.regs (waitSite (creditPoll gate)).result = some (.pred false) ∨
  s.pc = creditEnd gate + 2 ∧ s.fault = none ∨ creditEscape gate s.pc

private theorem healthyOfContinues {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) : s.fault = none := by
  cases hf : s.fault with
  | none => rfl
  | some f =>
    obtain ⟨tm, hOut, hFire⟩ := he
    have hFault : out kernel Assumptions.all l g s = .ev (.ub f) := by simp [out, hf]
    obtain rfl := Out.ev.inj (hOut.symm.trans hFault)
    cases hFire.2

private theorem failCredit {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (gate : CreditGate) (hPc : s.pc = creditEnd gate)
    (he : EStep kernel Assumptions.all l g s e (some u))
    (hFailed : ¬ successCredit gate e) : beforeCredit gate u := by
  let spec := waitSite (creditPoll gate)
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source he
  change s.pc = (waitSite (creditPoll gate)).pc at hPc
  rw [hPc, (waitCode (creditPoll gate)).1] at hc
  obtain rfl := Option.some.inj hc.symm
  cases hLoc : mbarLoc l g s spec.base 0 with
  | error f =>
    simp [eventTmpl, tmaTmpl, spec, hLoc, bind, Except.bind, ofExec, widenMbarScope, Fires] at hFire
  | ok loc =>
    cases hWord : readBits l g s 32 (.reg spec.phase) with
    | error f =>
      simp [eventTmpl, tmaTmpl, spec, hLoc, hWord, bind, Except.bind, ofExec,
        widenMbarScope, Fires] at hFire
    | ok word =>
      obtain ⟨pass, acq, scope, hE, hNext⟩ := fires_wait_at hLoc hWord hFire
      cases pass
      · obtain rfl := hNext u rfl
        exact .inr (.inl ⟨by simp [next, setReg, hPc, creditEnd], by
          simpa [next, setReg] using healthyOfContinues he, by simp [next, setReg]⟩)
      · exact (hFailed ⟨by rw [hE]; exact hPc, loc, word.toNat % 2, acq, scope,
          by rw [hE]⟩).elim

private theorem noCreditStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (gate : CreditGate) (hs : beforeCredit gate s)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hFailed : ∀ e ∈ ev.toList, ¬ successCredit gate e) : beforeCredit gate u := by
  let spec := waitSite (creditPoll gate)
  rcases hs with hs | ⟨hPc, hHealthy, hPred⟩ | ⟨hPc, hHealthy⟩ | hExit
  · by_cases hLt : s.pc < creditEnd gate
    · rcases withinCreditRange gate hs hLt hStep with h | h
      · exact .inl h
      · exact .inr (.inr (.inr h))
    · have hPc : s.pc = creditEnd gate := by have := hs.2; omega
      rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
      · obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
        change s.pc = (waitSite (creditPoll gate)).pc at hPc
        rw [hPc, (waitCode (creditPoll gate)).1] at hc
        obtain rfl := Option.some.inj hc.symm
        rcases hExec with ⟨_, h⟩ | ⟨_, h, _⟩ <;> cases h
      · exact failCredit gate hPc he (hFailed e (by simp))
  · have hc : kernel.code[s.pc]? =
        some ⟨some (spec.result, false), .bra (spec.pc + 3) true⟩ :=
      hPc.symm ▸ (waitCode (creditPoll gate)).2.1
    have hTau : Tau kernel Assumptions.all l g s (skip s) := by
      change s.regs spec.result = some (.pred false) at hPred
      unfold Tau
      simp [out, hHealthy, hc, guardHolds, readReg, hPred, bind, Except.bind, pure, Except.pure]
    rcases hStep with ⟨rfl, ht⟩ | ⟨_, rfl, he⟩
    · obtain rfl := tau_det ht hTau
      exact .inr (.inr (.inl ⟨by simp [skip, hPc, Nat.add_assoc], hHealthy⟩))
    · exact (not_tau_of_stops (stops_of_estep he) hTau).elim
  · have hc : kernel.code[s.pc]? = some ⟨none, .bra spec.pc true⟩ :=
      hPc.symm ▸ (waitCode (creditPoll gate)).2.2
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      rw [hPc]
      cases gate <;> (try cases ‹Thread.Scores.Round›) <;> decide
    have hTau : Tau kernel Assumptions.all l g s {s with pc := spec.pc} := by
      apply tauStep_iff.mp
      rw [Assumptions.tauStep_all_eq_nil hOff hc rfl]
      simp [tauStep, out, hHealthy, hc, guardHolds, Op.isLocal, execLocalA, execLocalRule,
        execLocal, Op.rule, execBranch, pure, Except.pure]
    rcases hStep with ⟨rfl, ht⟩ | ⟨_, rfl, he⟩
    · obtain rfl := tau_det ht hTau
      have hLo : creditStart gate ≤ creditEnd gate := by
        cases gate <;> (try cases ‹Thread.Scores.Round›) <;> decide
      exact .inl ⟨hLo, le_rfl⟩
    · exact (not_tau_of_stops (stops_of_estep he) hTau).elim

  · cases gate with
    | publication => cases hExit
    | terminal => cases hExit
    | entry => exact .inr (.inr (.inr (remainsEscaped hExit hStep)))

private theorem creditPathBlocked {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (gate : CreditGate) (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : beforeCredit gate s) (hNone : ∀ e ∈ es, ¬ successCredit gate e) :
    beforeCredit gate u := by
  induction h with
  | refl => exact hs
  | tau ht _ ih =>
    apply ih (noCreditStep gate hs (.inl ⟨rfl, ht⟩) (by simp)) hNone
  | @event _ _ _ es e he _ ih =>
    refine ih (noCreditStep gate hs (.inr ⟨e, rfl, he⟩) ?_) ?_
    · intro x hx
      have hx' : x = e := by simpa using hx
      subst x
      exact hNone e (by simp)
    · intro x hx
      exact hNone x (List.mem_cons_of_mem _ hx)
private theorem publicationSite {e : Event} {round : Thread.Scores.Round}
    (h : Thread.Scores.notice e = some round) : e.pc = publicationPc round := by
  unfold Thread.Scores.notice at h
  split at h <;> try contradiction
  unfold Thread.Scores.noticeRound at h
  split at h <;> cases round <;> simp_all [publicationPc]

private theorem publicationCode (round : Thread.Scores.Round) :
    kernel.code[publicationPc round]? = some ⟨none, .barArrive (.reg 5127) (.imm 64) true⟩ := by
  cases round
  · exact Flow.code_4397
  · exact Flow.code_5683
  · exact Flow.code_6891
  · exact Flow.code_7616

/-- This actual event acquires a reusable statistics buffer. -/
@[no_expose] def StatsCreditAcquired (X : Execution) (i : EvId) : Prop :=
  ∃ e, X.get i = some e ∧ e.pc ∈ [3420, 4874, 6558, 7463, 7738] ∧
    ∃ loc parity acq scope, e.kind = .wait loc parity true acq scope

/-- The successful acquire on the role's terminal route. -/
@[no_expose] def TerminalCredit (X : Execution) (i : EvId) : Prop :=
  ∃ e, X.get i = some e ∧ successCredit .terminal e

theorem TerminalCredit.acquired {X : Execution} {i : EvId} (h : TerminalCredit X i) :
    StatsCreditAcquired X i := by
  obtain ⟨e, he, hPc, hWait⟩ := h
  exact ⟨e, he, by rw [hPc]; decide, hWait⟩

/-- The marker in the role machine records precisely a successful statistics acquire. -/
theorem creditAcquiredOfObservation {X : Execution} {i : EvId} {e : Event}
    (he : X.get i = some e) (hm : Thread.Scores.creditAcquired e = true) :
    StatsCreditAcquired X i := by
  unfold Thread.Scores.creditAcquired at hm
  split at hm
  · rename_i loc parity acq scope hKind
    exact ⟨e, he, List.contains_iff_mem.mp hm, loc, parity, acq, scope, hKind⟩
  · cases hm

/-- A successful statistics acquire advances the role's credit cursor. -/
theorem creditObservationOfAcquire {X : Execution} {i : EvId} (ha : StatsCreditAcquired X i) :
    ∃ e, X.get i = some e ∧ Thread.Scores.creditAcquired e = true := by
  obtain ⟨e, he, hSite, loc, q, acq, scope, hk⟩ := ha
  refine ⟨e, he, ?_⟩
  simp only [Thread.Scores.creditAcquired, hk]
  simpa using hSite

private theorem creditBetweenPublicationAndEvent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {a : Thread.Scores.Round} {f : Event}
    (hi : Thread.Scores.Publishes X (g,i) a) (hf : X.get (g,j) = some f)
    (hOutside : ¬ (creditStart (.publication a) ≤ f.pc ∧
      f.pc ≤ creditEnd (.publication a) + 2))
    (hLt : i < j) : ∃ k, i < k ∧ k < j ∧ StatsCreditAcquired X (g,k) := by
  obtain ⟨e, he, hA⟩ := hi
  have hG := event_thread_lt hX he
  obtain ⟨_, hRun⟩ := hX.thr g hG
  have hJ : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).1
  have hiBound : i+1 < (X.tr g).length := by omega
  obtain ⟨s, u, hFirst, hTail⟩ := hRun.after_event he hiBound
  have hAt := (estep_source_pc hFirst).symm.trans (publicationSite hA)
  have hNext := followsMarkedBarrier hAt (publicationCode a) rfl hFirst
  have hStart : u.pc = creditStart (.publication a) := by rw [hNext, hAt]; rfl
  let offset := j - (i+1)
  have hOffset : i+1+offset = j := by dsimp [offset]; omega
  have hf' : ((X.tr g).drop (i+1))[offset]? = some f := by
    rw [List.getElem?_drop, hOffset]
    exact hf
  obtain ⟨v, _, hPath, hLast⟩ := hTail.before_event hf'
  by_contra hNone
  have hBlocked := creditPathBlocked (.publication a) hPath
    (.inl ⟨by rw [hStart], by rw [hStart]; cases a <;> decide⟩) (by
      intro x hx hSuccess
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      have hLim := (List.getElem?_eq_some_iff.mp hk).1
      simp only [List.length_take] at hLim
      have hK : k < offset := by omega
      rw [List.getElem?_take_of_lt hK, List.getElem?_drop] at hk
      have hh : X.get (g,i+1+k) = some x := hk
      have hMember : x.pc ∈ [3420, 4874, 6558, 7463, 7738] := by
        rw [hSuccess.1]
        cases a <;> decide
      exact hNone ⟨i+1+k, by omega, by omega, x, hh, hMember, hSuccess.2⟩)
  have hLo : creditStart (.publication a) ≤ v.pc := by
    have hSE : creditStart (.publication a) ≤ creditEnd (.publication a) := by cases a <;> decide
    rcases hBlocked with h | h | h | h
    · exact h.1
    · omega
    · omega
    · cases h
  have hHi : v.pc ≤ creditEnd (.publication a) + 2 := by
    rcases hBlocked with h | h | h | h
    · have := h.2
      omega
    · omega
    · omega
    · cases h
  rw [← estep_source_pc hLast] at hLo hHi
  exact hOutside ⟨hLo, hHi⟩

/-- Reusing the statistics rendezvous requires an actual successful credit acquire since the
lane's earlier publication. This applies to suspended finite prefixes. -/
theorem creditBetweenPublications {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {a b : Thread.Scores.Round}
    (hi : Thread.Scores.Publishes X (g,i) a) (hj : Thread.Scores.Publishes X (g,j) b)
    (hLt : i < j) : ∃ k, i < k ∧ k < j ∧ StatsCreditAcquired X (g,k) := by
  obtain ⟨f, hf, hB⟩ := hj
  refine creditBetweenPublicationAndEvent hX hi hf ?_ hLt
  rintro ⟨hLo, hHi⟩
  have hFails := noLaterPublicationInCreditRange a hLo hHi
  rw [publicationSite hB] at hFails
  exact hFails (by cases b <;> decide)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem initialCreditBeforeEvent {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hWide : 3422 < e.pc ∧ e.pc < 7733) :
    ∃ k < j, StatsCreditAcquired X (g,k) := by
  have hRange : 3420 ≤ e.pc ∧ e.pc < 7742 := by omega
  obtain ⟨w, _, pos, s, _, hPos, hs, hr⟩ := softmaxBodySuffix hp hX he hRange.1 hRange.2
  let n := j-pos
  have he' : ((X.tr g).drop pos)[n]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨u, _, hPath, hStep⟩ := hr.before_event he'
  by_contra hNone
  have hStart : beforeCredit .entry s := .inl ⟨by rw [hs.1]; decide, by rw [hs.1]; decide⟩
  have hBlocked := creditPathBlocked .entry hPath hStart (by
    intro f hf hSuccess
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hf
    have hLim := (List.getElem?_eq_some_iff.mp hk).1
    simp only [List.length_take] at hLim
    have hK : k < n := by omega
    rw [List.getElem?_take_of_lt hK, List.getElem?_drop] at hk
    have hGet : X.get (g,pos+k) = some f := hk
    have hMember : f.pc ∈ [3420, 4874, 6558, 7463, 7738] := by rw [hSuccess.1]; decide
    exact hNone ⟨pos+k, by dsimp [n] at hK; omega, f, hGet, hMember, hSuccess.2⟩)
  have hPc : u.pc = e.pc := (estep_source_pc hStep).symm
  rcases hBlocked with h | h | h | h <;> rw [hPc] at h
  · have hEnd : e.pc ≤ 3420 := h.2
    omega
  · have hCheck : e.pc = 3421 := h.1
    omega
  · have hRetry : e.pc = 3422 := h.1
    omega
  · exact (not_le_of_gt hWide.2) h

/-- Any statistics publication was preceded by the initial acquire of the statistics buffer. -/
theorem initialCreditBeforePublication {g j : Nat} {round : Thread.Scores.Round}
    (hPub : Thread.Scores.Publishes X (g,j) round) :
    ∃ k < j, StatsCreditAcquired X (g,k) := by
  obtain ⟨e, he, hNotice⟩ := hPub
  exact initialCreditBeforeEvent hp hX he (by rw [publicationSite hNotice]; cases round <;> decide)

/-- The successful credit poll is on the statistics buffer shared by the issuer's stage. -/
theorem creditAcquireObject {i : EvId} (h : StatsCreditAcquired X i) :
    ∃ e q acq scope, X.get i = some e ∧
      e.kind = .wait
        ⟨.shared, i.1 / l.block, l.sharedBase + (192 + 8 * (Prologue.warpIndex l i.1 / 4))⟩
        q true acq scope := by
  obtain ⟨e, he, hSite, loc, q, acq, scope, hk⟩ := h
  have ee : e = ⟨e.pc, .wait loc q true acq scope⟩ := by
    cases e
    exact congrArg (Event.mk _) hk
  have hLoc := softmaxStatsCreditWaitAddress hp hX (he.trans (congrArg some ee)) hSite
  exact ⟨e, q, acq, scope, he, hLoc ▸ hk⟩

omit hp hX in
private theorem acquiredBefore_count_succ {X : Execution} {g k : Nat}
    (ha : StatsCreditAcquired X (g,k)) :
    ((X.tr g).take (k+1)).countP Thread.Scores.creditAcquired =
      ((X.tr g).take k).countP Thread.Scores.creditAcquired + 1 := by
  obtain ⟨e, he, hMark⟩ := creditObservationOfAcquire ha
  exact countP_take_succ he hMark

/-- Every reached statistics publication has acquired its buffer once for this publication and
once for each earlier one of the lane. -/
theorem creditCursorBeforePublication {g j : Nat} {round : Thread.Scores.Round}
    (hPub : Thread.Scores.Publishes X (g,j) round) :
    (Thread.Scores.before X (g,j)).notices + 1 ≤ (Thread.Scores.before X (g,j)).credits := by
  rw [Thread.Scores.beforeNotices, Thread.Scores.beforeCredits]
  change ((X.tr g).take j).countP Thread.Scores.publishesStats + 1 ≤
    ((X.tr g).take j).countP Thread.Scores.creditAcquired
  induction j using Nat.strong_induction_on generalizing round with
  | h j ih =>
    let publications := ((X.tr g).take j).countP Thread.Scores.publishesStats
    by_cases hNone : publications = 0
    · change publications + 1 ≤ _
      obtain ⟨k, hk, ha⟩ := initialCreditBeforePublication hp hX hPub
      have hc := acquiredBefore_count_succ ha
      have hMono := countP_take_mono Thread.Scores.creditAcquired (X.tr g) (i := k+1) (j := j)
        (by omega)
      omega
    · have hN : publications - 1 < publications := by omega
      obtain ⟨i, hi, e, he, hm, hOrd⟩ := exists_nth Thread.Scores.publishesStats (X.tr g)
        (k := j) (n := publications - 1) hN
      obtain ⟨other, hNotice⟩ := Option.isSome_iff_exists.mp hm
      have hPrevious : Thread.Scores.Publishes X (g,i) other := ⟨e, he, hNotice⟩
      have hEarly := ih i hi hPrevious
      obtain ⟨k, hIk, hKj, ha⟩ := creditBetweenPublications hX hPrevious hPub hi
      have hMon₁ := countP_take_mono Thread.Scores.creditAcquired (X.tr g) hIk.le
      have hMon₂ := countP_take_mono Thread.Scores.creditAcquired (X.tr g) (i := k+1) (j := j)
        (by omega)
      have hc := acquiredBefore_count_succ ha
      change publications + 1 ≤ _
      change ((X.tr g).take i).countP Thread.Scores.publishesStats = publications - 1 at hOrd
      omega

/-- A reached statistics write has acquired its buffer for this generation, even when its
following publication has not been issued. -/
theorem creditCursorBeforeStatisticsStore {i : EvId} {site : Fin 4} {a : Acc} {bytes : List Byte}
    (hStore : Thread.Scores.StatisticsStore X i site a bytes) :
    (Thread.Scores.before X i).notices + 1 ≤ (Thread.Scores.before X i).credits := by
  rcases i with ⟨g, j⟩
  change X.get (g,j) = some ⟨(statsStore site).pc, .wr a bytes⟩ at hStore
  rw [Thread.Scores.beforeNotices, Thread.Scores.beforeCredits]
  let publications := ((X.tr g).take j).countP Thread.Scores.publishesStats
  change publications + 1 ≤ ((X.tr g).take j).countP Thread.Scores.creditAcquired
  by_cases hNone : publications = 0
  · have hSite : 3422 < (statsStore site).pc ∧ (statsStore site).pc < 7733 := by
      fin_cases site <;> decide
    obtain ⟨k, hk, hCredit⟩ := initialCreditBeforeEvent hp hX hStore hSite
    have hStep := acquiredBefore_count_succ hCredit
    have hMono := countP_take_mono Thread.Scores.creditAcquired (X.tr g)
      (i := k + 1) (j := j) (by omega)
    omega
  · obtain ⟨prior, hPrior, e, he, hMark, hNumber⟩ :=
      exists_nth Thread.Scores.publishesStats (X.tr g) (k := j) (n := publications - 1)
        (show publications - 1 < publications by omega)
    obtain ⟨round, hNotice⟩ := Option.isSome_iff_exists.mp hMark
    have hPub : Thread.Scores.Publishes X (g,prior) round := ⟨e, he, hNotice⟩
    have hOutside : ¬ (creditStart (.publication round) ≤ (statsStore site).pc ∧
        (statsStore site).pc ≤ creditEnd (.publication round) + 2) := by
      cases round <;> fin_cases site <;> decide
    obtain ⟨k, hBefore, hAfter, hCredit⟩ :=
      creditBetweenPublicationAndEvent hX hPub hStore hOutside hPrior
    have hEarly := creditCursorBeforePublication hp hX hPub
    rw [Thread.Scores.beforeNotices, Thread.Scores.beforeCredits] at hEarly
    dsimp only at hEarly
    have hStep := acquiredBefore_count_succ hCredit
    have hMono₁ := countP_take_mono Thread.Scores.creditAcquired (X.tr g) hBefore.le
    have hMono₂ := countP_take_mono Thread.Scores.creditAcquired (X.tr g)
      (i := k + 1) (j := j) (by omega)
    change ((X.tr g).take prior).countP Thread.Scores.publishesStats =
      publications - 1 at hNumber
    omega

omit hp hX in
private theorem terminalCreditOnSuffix {l : Launch} {X : Execution} {g i j : Nat}
    {s : TState} {o : Option TState}
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop i) o)
    (hStart : creditRange .terminal s.pc) (hi : i ≤ j)
    (hExit : X.get (g,j) = some ⟨9205,.exit⟩) :
    ∃ k, i ≤ k ∧ k < j ∧ TerminalCredit X (g,k) := by
  let distance := j-i
  have hTerminal : ((X.tr g).drop i)[distance]? = some ⟨9205,.exit⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hi]
    exact hExit
  obtain ⟨t, _, hPrefix, hLast⟩ := hr.before_event hTerminal
  by_contra hNone
  have hStuck := creditPathBlocked .terminal hPrefix (.inl hStart) (by
    intro e he hSuccess
    obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp he
    have hLen := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [List.length_take] at hLen
    have hk : k < distance := by omega
    rw [List.getElem?_take_of_lt hk, List.getElem?_drop] at hGet
    exact hNone ⟨i+k, by omega, by dsimp [distance] at hk; omega, e, hGet, hSuccess⟩)
  have hPc := (estep_source_pc hLast).symm
  change t.pc = 9205 at hPc
  rcases hStuck with h | h | h | h
  · have hBound : t.pc ≤ 7738 := h.2
    omega
  · have hCheck : t.pc = 7739 := h.1
    omega
  · have hRetry : t.pc = 7740 := h.1
    omega
  · cases h

omit hp hX in
private theorem terminalCreditAfterPublication {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {round : Thread.Scores.Round} (hPub : Thread.Scores.Publishes X (g,i) round)
    (hExit : X.get (g,j) = some ⟨9205,.exit⟩) (hLt : i < j) :
    ∃ k, i < k ∧ k < j ∧ TerminalCredit X (g,k) := by
  obtain ⟨e, he, hNotice⟩ := hPub
  obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hExit).1
  obtain ⟨s, u, hPubStep, hTail⟩ := hRun.after_event he (by omega)
  have hPc := (estep_source_pc hPubStep).symm.trans (publicationSite hNotice)
  have hNext := followsMarkedBarrier hPc (publicationCode round) rfl hPubStep
  have hRange : creditRange .terminal u.pc := by
    rw [hNext, hPc]
    cases round <;> decide
  obtain ⟨k, hK, hBefore, hAcq⟩ := terminalCreditOnSuffix hTail hRange (by omega) hExit
  exact ⟨k, by omega, hBefore, hAcq⟩

/-- A softmax lane acquires its terminal credit after all its statistics publications. -/
theorem terminalCreditBeforeExit {g j : Nat} {e : Event} (hw : Prologue.warpIndex l g < 8)
    (he : X.get (g,j) = some e) (hKind : e.kind = .exit) :
    ∃ k < j, TerminalCredit X (g,k) ∧
      (Thread.Scores.before X (g,j)).notices ≤ (Thread.Scores.before X (g,k)).credits := by
  have hExit : X.get (g,j) = some ⟨9205,.exit⟩ := by
    obtain ⟨pc, kind⟩ := e
    change kind = .exit at hKind
    subst kind
    rw [actualExitPc hX he] at he
    exact he
  rw [Thread.Scores.beforeNotices]
  let n := ((X.tr g).take j).countP Thread.Scores.publishesStats
  change ∃ k < j, TerminalCredit X (g,k) ∧ n ≤ (Thread.Scores.before X (g,k)).credits
  by_cases hZero : n = 0
  · obtain ⟨_, _, pos, s, _, hPos, hAt, hr⟩ :=
      softmaxRoleEntrySuffix hp hX hExit (by decide) (by decide) hw
    obtain ⟨k, _, hKj, hAcq⟩ := terminalCreditOnSuffix hr (by rw [hAt.1]; decide) hPos hExit
    exact ⟨k, hKj, hAcq, hZero.symm ▸ Nat.zero_le _⟩
  · have hn : n-1 < n := by omega
    obtain ⟨i, hIj, f, hf, hm, hOrd⟩ := exists_nth Thread.Scores.publishesStats (X.tr g)
      (k := j) (n := n-1) hn
    obtain ⟨round, hNotice⟩ := Option.isSome_iff_exists.mp hm
    have hPub : Thread.Scores.Publishes X (g,i) round := ⟨f, hf, hNotice⟩
    obtain ⟨k, hIk, hKj, hAcq⟩ := terminalCreditAfterPublication hX hPub hExit hIj
    have hCredits := creditCursorBeforePublication hp hX hPub
    rw [Thread.Scores.beforeNotices, Thread.Scores.beforeCredits] at hCredits
    change ((X.tr g).take i).countP Thread.Scores.publishesStats + 1 ≤
      ((X.tr g).take i).countP Thread.Scores.creditAcquired at hCredits
    have hMono := countP_take_mono Thread.Scores.creditAcquired (X.tr g) hIk.le
    refine ⟨k, hKj, hAcq, ?_⟩
    rw [Thread.Scores.beforeCredits]
    change n ≤ ((X.tr g).take k).countP Thread.Scores.creditAcquired
    omega

end PTX.Kernels.TmlFa4Fwd.Softmax
