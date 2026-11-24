-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreActive
import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityScoreOrder
import Lemmas.Order.GuardOrder
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.Flow Thread.Scores
open PTX.MBarrier hiding okPolls

/-- The final MMA's joint probability wait witnesses a softmax credit at least as recent
as the issued score commit, even if the score notification was initially pending. -/
private theorem terminalCreditOfScore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {out score : EvId} {cta : Nat} {stage : Fin 2} {s spec : TcCommit.Spec} {rank : Fin 16}
    (hOut : TerminalOutputCommit X stage out s) (hCta : out.1 / l.block = cta)
    (hScore : ScoreCommit l X score cta stage spec rank) :
    ∃ credit, ProbabilityCredit l X credit cta stage 0 ∧
      Prologue.warpIndex l credit.1 < 8 ∧
      scoreCommitOrdinal l X cta stage score ≤ probabilityOrdinal l X cta stage 0 credit ∧
      Relation.TransGen (DepStep l kernel X) (.thread credit, false) (.thread out, false) := by
  let loc := probabilityObject l cta stage 0
  let log := X.objects loc
  obtain ⟨k, ⟨_, kind⟩, q, acq, scope, hGet, hKind, hBudget, hResume⟩ :=
    terminalOutputProbabilityAfterScore hp hX hOut hCta hScore
  change kind = _ at hKind
  subst kind
  let n := okPolls loc ((X.tr out.1).take k)
  have hNth := MbarRing.Poll.nth_eq hGet
  have hLt : n < okPolls loc (X.tr out.1) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none :=
    fun _ hr hs => actualInitOrPollClean hp hX hr (.inr hs)
  obtain ⟨i, w, _, hW, hId, _, hOk, _, _⟩ := MbarRing.Poll.record hX hClean hLt
  rw [hNth] at hId
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hAlt := probabilitySelectedAlternates hp hX (g := out.1) (cta := cta) stage 0
  have hSelected := objectThreadSelected_iff.mpr ⟨_, hId⟩
  obtain ⟨st, hs, hLower, _⟩ := (X.objects_checked hX loc).selected_poll_phase_ge hNo
    (objectThreadSelected out.1) (by decide) hAlt hW hSelected hOk
  obtain ⟨st', _, hs', _, _, hCompleted⟩ := (X.objects_checked hX loc).okPoll hW hOk
  have hEq : st' = st := Option.some.inj (hs'.symm.trans hs)
  subst st'
  have hPositive : 0 < st.phase := by omega
  have hAt : observedAt log i = some (st.phase - 1) := by
    change log[i]?.bind (·.reply.completed) = _
    rw [hW, Option.bind_some, hCompleted, ite_eq_left hPositive]
  obtain ⟨credit, hCredit, hRole, hOrdinal, hSeen⟩ :=
    jointPollObservesSoftmax hp hX (correctionJointGuardsOfCuQ hp hX hCuQ) stage hW hOk hAt
  rw [hId] at hSeen
  change scoreCommitOrdinal l X cta stage score ≤ n at hBudget
  exact ⟨credit, hCredit, hRole, by omega,
    (Relation.TransGen.single (DepStep.of_witness l (Witness.of_mbarObserved hSeen))).tail
      (DepStep.of_resumes l hResume)⟩

/-- A successful score wait orders the notification of any score already completed by its
observed phase. Earlier generations use the score object's recorded order. -/
private theorem scoreBeforePoll {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta j phase : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X e cta stage spec rank) {poll : Record Ref}
    (hPoll : (X.objects (scoreReadyObject l cta stage))[j]? = some poll)
    (hOk : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (scoreReadyObject l cta stage)) j = some phase)
    (hLe : scoreCommitOrdinal l X cta stage e ≤ phase) :
    rank ∈ X.tcNotified e ∧
      MBarrier.Before (X.objects (scoreReadyObject l cta stage)) (.async e (.tcNotify rank))
        poll.id := by
  classical
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  let n := scoreCommitOrdinal l X cta stage e
  have hChecked := X.objects_checked hX loc
  have hInit := scoreReadyInitialized hp hX stage (List.mem_of_getElem? hPoll)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have unit {r : Record Ref} (hr : r ∈ log) (h : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,_,_,_,ha⟩ := scoreReadyUpdate hp hX stage hr h
    exact ha
  have hInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hInc
    have h := unit hr (by rw [hInc]; trivial)
    rw [hInc] at h
    cases h
  obtain ⟨st, hs, hSt⟩ := hChecked.observed_phase hPoll hOk hPhase
  have hCard := hChecked.card_unit_arrivals_phase hNo (n := 1) (q := n)
    (fun _ r c tx hr _ ha => (Action.arrive.inj
      (ha.symm.trans (unit (List.mem_of_getElem? hr) (by rw [ha]; trivial)))).1)
    (fun _ _ _ ht => PairTmaRing.expected_of_init hX hInit hNo ht)
    hInc (List.getElem?_eq_some_iff.mp hPoll).1.le hs (by change n ≤ phase at hLe; omega)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < _ from hCard.symm ▸ Nat.zero_lt_one)
  obtain ⟨_, r, _, hr, ha, _, hAt⟩ := Finset.mem_filter.mp hi
  have hUpdate : CounterUpdate r.action := by rw [ha]; trivial
  obtain ⟨other, found, observed, hid, hc, ht, _, _⟩ :=
    scoreReadyUpdate hp hX stage (List.mem_of_getElem? hr) hUpdate
  have hOrdinal := Option.some.inj
    ((scoreNotificationPhaseExact hp hX stage hr hUpdate hid).2.symm.trans hAt)
  obtain ⟨rfl, rfl⟩ := scoreCommitOrdinalInjective hp hX ⟨hc, ht⟩ hIssue hOrdinal
  have hOrder : i < j := by
    by_contra hBad
    obtain ⟨u, hu, hMono⟩ := hChecked.phase_mono hNo (Nat.le_of_not_lt hBad)
      (List.getElem?_eq_some_iff.mp hr).1.le hs
    have hU : u.phase = n := by
      change (stateBefore log i).map (·.phase) = some n at hAt
      rwa [hu, Option.map_some, Option.some.injEq] at hAt
    change n ≤ phase at hLe
    omega
  have hPresent := object_record_present hX.tma (List.mem_of_getElem? hr)
  rw [hid] at hPresent
  exact ⟨hPresent, i, j, r, poll, hr, hid, hPoll, rfl, hOrder⟩

/-- All issued score-ready notifications finish before the correction lane can exit.
The final probability wait supplies the credits even for a score in an earlier generation. -/
theorem scoreNotificationFinishedAtExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {e : EvId} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X e (e.1 / l.block) stage spec rank)
    (hExit : CtaExited l X (e.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async e (.tcNotify rank)) (e.1 / l.block) := by
  obtain ⟨_, he⟩ := hIssue.1
  have hGrid := NamedBar.cta_lt (PTX.Proof.event_thread_lt hX he)
  have hWork := scoreCommitActive hp hX hCuQ hIssue
  have finish {out wait exit : EvId} {oSpec : TcCommit.Spec} {oRank : Fin 16}
      {object : Loc} {scope : MbarScope}
      (hOut : TerminalOutputCommit X stage out oSpec) (hCommit : X.Commit out oSpec)
      (hCta : out.1 / l.block = e.1 / l.block) (hNotified : oRank ∈ X.tcNotified out)
      (hObserved : WaitObserves X (.async out (.tcNotify oRank)) wait object true scope)
      (hResume : Resumes kernel X wait exit) (hOwner : OwnerExit l X (e.1 / l.block) exit) :
      SharedFinished l kernel Assumptions.all X (.async e (.tcNotify rank)) (e.1 / l.block) := by
    obtain ⟨credit, hCredit, hRole, hBound, hCreditOut⟩ :=
      terminalCreditOfScore hp hX hCuQ hOut hCta hIssue
    obtain ⟨k, j, phase, poll, hPoll, hId, hOk, hGuard, hPhase, hLe⟩ :=
      scoreObservedBeforeSoftmaxCredit hp hX stage 0 hRole hCredit
    obtain ⟨hPresent, hBefore⟩ := scoreBeforePoll hp hX hIssue hPoll hOk hPhase
      (hBound.trans hLe)
    rw [hId] at hBefore
    have hNote : X.AsyncPresent out (.tcNotify oRank) := hNotified
    obtain ⟨_, hCommitEvent⟩ := hCommit
    have hNotify : DepStep l kernel X (.thread out, false) (.async out (.tcNotify oRank), false) :=
      DepStep.issue ⟨_, hCommitEvent⟩ hNote
        (by intro t ht; cases ht) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    have hWitness := Witness.of_mbarObserved
      (mbarObserved_of_waitObserves hX.tma.2.2.1 hNote hObserved) (L := l)
    have hPath := (hCreditOut.head (DepStep.of_resumes l hGuard)).tail hNotify
    exact SharedFinished.of_completedBefore hPresent hOwner (CompletedBefore.of_before hBefore
      ((hPath.tail (DepStep.of_witness l hWitness)).tail (DepStep.of_resumes l hResume)))
  fin_cases stage
  · obtain ⟨out, s, r, w, scope, ex, hc, hC, _, hn, ho, hr, hx⟩ :=
      Thread.terminalFirstOutputObservedBeforeExit hp hX hGrid hWork hExit
    exact finish hc hc.issued hC hn ho hr hx
  · obtain ⟨out, s, r, w, scope, ex, hc, hC, _, hn, ho, hr, hx⟩ :=
      Thread.terminalOutputObservedBeforeExit hp hX hGrid hWork hExit
    exact finish hc hc.issued hC hn ho hr hx

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
