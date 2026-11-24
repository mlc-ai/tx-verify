-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOperandReady
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScoreRounds
public import Kernels.TmlFa4Fwd.Proof.MmaRecurringKeyPack
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem qkFragmentAtOrBefore {g index : Nat} {block : Fin 4} {n : Nat} {step : Fin 8}
    (hStep : step.val ≤ n) (hn : n < 8) {d : Nat} {op : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hMma : QkInstruction X (g, index) block ⟨n, hn⟩ d op acc mask) :
    ∃ j, j + n = index + step.val ∧ ∃ d' op' acc' mask',
      QkInstruction X (g, j) block step d' op' acc' mask' := by
  induction n using Nat.strong_induction_on generalizing index d op acc mask with
  | h n ih =>
    by_cases hEq : step.val = n
    · have hFragment : (⟨n, hn⟩ : Fin 8) = step := Fin.ext hEq.symm
      exact ⟨index, by omega, d, op, acc, mask, hFragment ▸ hMma⟩
    · have hPositive : 0 < n := by omega
      obtain ⟨j, hIndex, d', op', acc', mask', hPrevious⟩ :=
        hMma.previousFragmentAdjacent hp hX hPositive
      have hLt : n - 1 < n := by omega
      obtain ⟨k, hPos, hFound⟩ :=
        ih (n - 1) hLt (index := j) (by omega) (by omega) hPrevious
      exact ⟨k, by omega, hFound⟩

private theorem qkBankOfLast {g index : Nat} {block : Fin 4} {d : Nat} {op : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hLast : QkInstruction X (g, index) block 7 d op acc mask) :
    ∃ start, start + 7 = index ∧ ∀ step : Fin 8, ∃ d' op' acc' mask',
      QkInstruction X (g, start + step.val) block step d' op' acc' mask' := by
  obtain ⟨start, hStart, _⟩ :=
    qkFragmentAtOrBefore hp hX (step := 0) (by decide : (0 : Fin 8).val ≤ 7) (by decide) hLast
  have hEnd : start + 7 = index := by simpa using hStart
  refine ⟨start, hEnd, fun step => ?_⟩
  obtain ⟨j, hPos, hFound⟩ := qkFragmentAtOrBefore hp hX (step := step)
    (show step.val ≤ 7 by have := step.isLt; omega) (by decide) hLast
  have hAt : j = start + step.val := by omega
  exact hAt ▸ hFound

omit hp hX in
private theorem readyBeforeQkBank {l : Launch} {X : Execution} {g start wait parity : Nat}
    {block : Fin 4} {slot : Fin 3}
    (hBank : ∀ step : Fin 8, ∃ d op acc mask,
      QkInstruction X (g, start + step.val) block step d op acc mask)
    (hReady : Mma.ReadyPoll l X g wait slot parity true .cta) (hLast : wait < start + 7) :
    wait < start := by
  by_contra! hTooLate
  let step : Fin 8 := ⟨wait - start, by omega⟩
  obtain ⟨_, _, _, _, hFragment⟩ := hBank step
  have hPos : start + step.val = wait := by dsimp [step]; omega
  have hGet := hFragment.decoded
  rw [hPos] at hGet
  obtain ⟨event, hReadyGet, hKind⟩ := hReady
  have hEqual := congrArg Event.kind (Option.some.inj (hGet.symm.trans hReadyGet))
  rw [hKind] at hEqual
  exact Kind.noConfusion hEqual

/-- An issued last QK fragment certifies every actual fragment in its bank.
Their shared successful cache-ready acquire precedes all eight fragments. -/
theorem QkInstruction.observedBank {g index : Nat} {block : Fin 4} {d : Nat}
    {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hLast : QkInstruction X (g, index) block 7 d op acc mask) :
    ∃ (start wait : Nat) (slot : Fin 3) (parity : Nat), start + 7 = index ∧
      Mma.ReadyPoll l X g wait slot parity true .cta ∧
      ∀ step : Fin 8, ∃ d' op' acc' mask',
        QkInstruction X (g, start + step.val) block step d' op' acc' mask' ∧
        TraceBefore X (g, wait) (g, start + step.val) := by
  obtain ⟨start, hEnd, hBank⟩ := qkBankOfLast hp hX hLast
  have hIssue : X.MmaIssue (g, index) d op acc mask := ⟨_, hLast.decoded⟩
  obtain ⟨_, wait, slot, parity, _, hReady, hResumes, _⟩ :=
    Mma.actualMmaOperandReady hp hX hIssue
  have hBefore := readyBeforeQkBank hBank hReady (hEnd.symm ▸ hResumes.1.2.1)
  refine ⟨start, wait, slot, parity, hEnd, hReady, fun step => ?_⟩
  obtain ⟨d', op', acc', mask', hFragment⟩ := hBank step
  exact ⟨d', op', acc', mask', hFragment,
    ⟨rfl, by omega, len_of_get hFragment.decoded⟩⟩

/-- Each issued steady K release certifies both actual QK banks between its
matched ready acquire and issue, including before the notification is delivered. -/
theorem Mma.recurringKeyBankOfMatch {loc : Loc} {g release : Nat} {form : Mma.ReleaseForm}
    {spec : TcCommit.Spec} (hRelease : Mma.ReleaseIssue X g release form spec)
    (matched : Mma.ReleaseMatch l X g release form loc) (hForm : form = .loopKey) (stage : Fin 2) :
    ∃ start, ∀ step : Fin 8, ∃ d operands accum mask,
      QkInstruction X (g, start + step.val)
        (PTX.Kernels.TmlFa4Fwd.Mma.recurringKeyBlock stage) step d operands accum mask ∧
      TraceBefore X (g, matched.wait) (g, start + step.val) ∧
      TraceBefore X (g, start + step.val) (g, release) := by
  let block := PTX.Kernels.TmlFa4Fwd.Mma.recurringKeyBlock stage
  have hBlock : (if stage = 0 then (2 : Fin 4) else 3) = block := by
    fin_cases stage <;> rfl
  have hIssue : Mma.ReleaseIssue X g release .loopKey spec := hForm ▸ hRelease
  obtain ⟨commit, spec, hCommit, hDecoded, hCount, _⟩ := hIssue.recurringScoreCommit hp hX stage
  rw [hBlock] at hDecoded
  obtain ⟨last, hPos, d, op, acc, mask, hi⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.qkLastFragmentAdjacentToScoreCommit hp hX block hDecoded
  obtain ⟨start, hLast, hBank⟩ := qkBankOfLast hp hX hi
  have hEq : commit - 1 = last + 1 := by omega
  rw [hEq] at hCount
  have hGet := hi.decoded
  change (X.tr g)[last]? = _ at hGet
  have hCountLast :
      Mma.readyOccurrence X g last .loopKey =
        1 + Mma.releaseOccurrence X g release .loopKey := by
    simpa [Mma.readyOccurrence, Mma.releaseIndex, List.take_add_one, hGet, List.countP_append,
      PTX.Kernels.TmlFa4Fwd.Mma.readyAtSite] using hCount
  have hRank : Mma.readyOccurrence X g matched.wait .loopKey =
      Mma.releaseOccurrence X g release .loopKey := hForm ▸ matched.ordinal
  have hEarlier : matched.wait < last := by
    by_contra! hTooLate
    have hMono := (List.take_sublist_take_left (l := X.tr g) hTooLate).countP_le
      (p := PTX.Kernels.TmlFa4Fwd.Mma.readyAtSite 2)
    change Mma.readyOccurrence X g last .loopKey ≤
      Mma.readyOccurrence X g matched.wait .loopKey at hMono
    omega
  have hReady := matched.ready
  have hStart := readyBeforeQkBank hBank hReady (hLast.symm ▸ hEarlier)
  refine ⟨start, fun step => ?_⟩
  obtain ⟨d, operands, accum, mask, hi⟩ := hBank step
  have hEnd := hCommit.2.1
  have := step.isLt
  exact ⟨d, operands, accum, mask, hi, ⟨rfl, by omega, len_of_get hi.decoded⟩,
    ⟨rfl, by omega, hCommit.2.2⟩⟩

/-- Every actual score commit, including in the steady loop, has all eight
operand fragments and the successful ready acquire for the same bank. -/
theorem Scores.ScoreCommit.observedCacheBankAdjacent {commit : EvId} {cta : Nat} {stage : Fin 2}
    {spec : TcCommit.Spec} {rank : Fin 16}
    (hCommit : Scores.ScoreCommit l X commit cta stage spec rank) :
    ∃ (block : Fin 4) (start wait : Nat) (slot : Fin 3) (parity : Nat),
      block.val % 2 = stage.val ∧ start + 9 = commit.2 ∧
      Mma.ReadyPoll l X commit.1 wait slot parity true .cta ∧
      ∀ step : Fin 8, ∃ d operands accum mask,
        QkInstruction X (commit.1, start + step.val) block step d operands accum mask ∧
        TraceBefore X (commit.1, wait) (commit.1, start + step.val) := by
  obtain ⟨g, index⟩ := commit
  obtain ⟨block, hStage, hEvent⟩ := Scores.scoreCommitSite hp hX hCommit
  obtain ⟨last, hBefore, _, _, _, _, hFragment⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.qkLastFragmentAdjacentToScoreCommit hp hX block hEvent
  obtain ⟨start, wait, slot, parity, hLast, hReady, hBank⟩ :=
    hFragment.observedBank hp hX
  exact ⟨block, start, wait, slot, parity, hStage, by omega, hReady, hBank⟩

omit hp hX in
private theorem keyReadyCountAtFragment {X : Execution} {g start : Nat} {block : Fin 4}
    (hBank : ∀ step : Fin 8, ∃ d op acc mask,
      QkInstruction X (g, start + step.val) block step d op acc mask)
    (j : Nat) (hj : j ≤ 8) :
    Mma.readyOccurrence X g (start + j) .loopKey =
      Mma.readyOccurrence X g start .loopKey := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨_, _, _, _, hIns⟩ := hBank ⟨j, by omega⟩
    have hGet := hIns.decoded
    change (X.tr g)[start + j]? = _ at hGet
    have hQuiet :
        Mma.readyOccurrence X g (start + (j + 1)) .loopKey =
          Mma.readyOccurrence X g (start + j) .loopKey := by
      rw [← Nat.add_assoc, Mma.readyOccurrence, Mma.readyOccurrence, List.take_add_one, hGet]
      simp [List.countP_append, PTX.Kernels.TmlFa4Fwd.Mma.readyAtSite]
    exact hQuiet.trans (ih (by omega))

/-- A recurring score commit gives its actual bank and the same logical K-use
ordinal on every fragment of that bank. -/
theorem Scores.ScoreCommit.recurringCacheBankOccurrence {g index cta : Nat} {stage : Fin 2}
    {spec : TcCommit.Spec} {rank : Fin 16}
    (hCommit : Scores.ScoreCommit l X (g, index) cta stage spec rank)
    (hPositive : 0 < Scores.scoreCommitOrdinal l X cta stage (g, index)) :
    ∃ start, start + 9 = index ∧ ∀ step : Fin 8, ∃ d operands accum mask,
      QkInstruction X (g, start + step.val)
        (PTX.Kernels.TmlFa4Fwd.Mma.recurringKeyBlock stage) step d operands accum mask ∧
      1 + Mma.releaseElections X g (start + step.val) .loopKey =
        Scores.scoreCommitOrdinal l X cta stage (g, index) := by
  let block := PTX.Kernels.TmlFa4Fwd.Mma.recurringKeyBlock stage
  obtain ⟨b, hStage, hRepeat, hGet⟩ := Scores.positiveScoreCommitRepeats hp hX hCommit hPositive
  have hBlock : b = block := by
    fin_cases stage <;> fin_cases b <;> first | rfl | contradiction
  subst b
  obtain ⟨last, hIndex, _, _, _, _, hLast⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.qkLastFragmentAdjacentToScoreCommit hp hX block hGet
  obtain ⟨start, hEnd, hBank⟩ := qkBankOfLast hp hX hLast
  obtain ⟨_, _, _, hVote, _⟩ := PTX.Kernels.TmlFa4Fwd.Mma.scoreCommitLeader hp hX block hGet
  have hElectionSite : (if stage = 0 then (2 : Fin 4) else 3) = block := by
    fin_cases stage <;> rfl
  have hVote' := hVote
  rw [← hElectionSite] at hVote'
  have hCount := PTX.Kernels.TmlFa4Fwd.Mma.recurringKeyReadyAtScoreElection hp hX stage hVote'
  rw [hElectionSite] at hCount
  have hCta : g / l.block = cta := (Scores.scoreCommitActor hp hX hCommit).1
  have hOrdinal := Scores.recurringScoreExactOrdinal hp hX stage hGet
  rw [hCta] at hOrdinal
  change Mma.readyOccurrence X g (index - 1) .loopKey = _ at hCount
  rw [← hOrdinal, show index - 1 = start + 8 by omega,
    keyReadyCountAtFragment hBank 8 le_rfl] at hCount
  refine ⟨start, by omega, fun step => ?_⟩
  obtain ⟨d, operands, accum, mask, hIssue⟩ := hBank step
  have hGate : (PTX.Kernels.TmlFa4Fwd.Mma.slotWait 2).pc + 3 ≤
        PTX.Kernels.TmlFa4Fwd.Mma.qkPc block + step.val ∧
      PTX.Kernels.TmlFa4Fwd.Mma.qkPc block + step.val ≤
        (PTX.Kernels.TmlFa4Fwd.Mma.slotElect 2).pc := by
    fin_cases stage <;> fin_cases step <;> decide
  have hBalance := PTX.Kernels.TmlFa4Fwd.Mma.pendingReadyBalance hp hX 2 hIssue.decoded hGate
  change Mma.readyOccurrence X g (start + step.val) .loopKey =
    1 + Mma.releaseElections X g (start + step.val) .loopKey at hBalance
  rw [keyReadyCountAtFragment hBank step.val (by have := step.isLt; omega), hCount] at hBalance
  exact ⟨d, operands, accum, mask, hIssue, hBalance.symm⟩

/-- A release of an earlier cache occurrence precedes a fragment whose correctly
matched gate has advanced past that release. -/
theorem Mma.ReleaseIssue.beforeLaterCacheFragment {g index commit d : Nat} {form : Mma.ReleaseForm}
    {spec : TcCommit.Spec} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hRelease : Mma.ReleaseIssue X g commit form spec)
    (hMma : X.MmaIssue (g, index) d op accum mask)
    (hRank : Mma.releaseOccurrence X g commit form < Mma.releaseElections X g index form) :
    TraceBefore X (g, commit) (g, index) := by
  have hPos := (PTX.Kernels.TmlFa4Fwd.Mma.readyReleaseElection hp hX
    (Mma.releaseIndex form) hRelease).1
  obtain ⟨pc, hGet⟩ := hMma
  refine ⟨rfl, ?_, len_of_get hGet⟩
  by_contra! hTooEarly
  rcases hTooEarly.lt_or_eq with hLater | rfl
  · have hMono := (List.take_sublist_take_left (l := X.tr g)
      (show index ≤ commit - 1 by omega)).countP_le
      (p := PTX.Kernels.TmlFa4Fwd.Mma.releaseAtSite (Mma.releaseIndex form))
    change Mma.releaseElections X g index form ≤ Mma.releaseOccurrence X g commit form at hMono
    omega
  · have hEq := congrArg Event.kind (Option.some.inj (hGet.symm.trans hRelease))
    cases hEq

/-- A positive score ordinal precedes every fragment of a later recurring key
bank in the same CTA, including across the two score stages. -/
theorem Scores.ScoreCommit.beforeLaterRecurringCacheBank {old : EvId} {g index cta : Nat}
    {oldStage stage : Fin 2} {previous spec : TcCommit.Spec} {oldRank rank : Fin 16}
    (hOld : Scores.ScoreCommit l X old cta oldStage previous oldRank)
    (hLater : Scores.ScoreCommit l X (g, index) cta stage spec rank)
    (hPositive : 0 < Scores.scoreCommitOrdinal l X cta oldStage old)
    (hEarlier : Scores.scoreCommitOrdinal l X cta oldStage old <
      Scores.scoreCommitOrdinal l X cta stage (g, index)) :
    ∃ start, start + 9 = index ∧ ∀ step : Fin 8, ∃ d operands accum mask,
      QkInstruction X (g, start + step.val)
        (PTX.Kernels.TmlFa4Fwd.Mma.recurringKeyBlock stage) step d operands accum mask ∧
      TraceBefore X old (g, start + step.val) := by
  obtain ⟨start, hStart, hBank⟩ := hLater.recurringCacheBankOccurrence hp hX (by omega)
  obtain ⟨_, _, _, _, _, hInitial⟩ := hBank 0
  change 1 + Mma.releaseElections X g start .loopKey =
    Scores.scoreCommitOrdinal l X cta stage (g, index) at hInitial
  let keep := PTX.Kernels.TmlFa4Fwd.Mma.releaseAtSite 2
  let phase := Scores.scoreCommitOrdinal l X cta oldStage old - 1
  have hLt : phase < ((X.tr g).take start).countP keep := by
    change phase < Mma.releaseElections X g start .loopKey
    dsimp only [phase]
    omega
  obtain ⟨j, hj, event, hEvent, hMark, hRound⟩ :=
    PTX.Flow.exists_nth keep (X.tr g) (k := start) (n := phase) hLt
  obtain ⟨tag, kind⟩ := event
  obtain ⟨block, _, hScore⟩ := Scores.scoreCommitSite hp hX hLater
  obtain ⟨_, _, _, hScoreVote, hLane⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.scoreCommitLeader hp hX block hScore
  cases kind <;> simp [keep, PTX.Kernels.TmlFa4Fwd.Mma.releaseAtSite, ElectOrd.atSites,
    isElectEv] at hMark
  case elect mask inst leader =>
    subst tag
    have hVote : X.Elect (g, j) (PTX.Kernels.TmlFa4Fwd.Mma.slotElect 2).pc mask inst leader :=
      hEvent
    have hMask := actualFullElectionMask hX hVote
    subst mask
    have hg := PTX.Proof.event_thread_lt hX hScore
    have hWarp : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
    have hLeader := PTX.Kernels.TmlFa4Fwd.Mma.sameLeader hX hWarp hScoreVote hVote
    have hLen : index < (X.tr g).length := len_of_get hScore
    obtain ⟨s, hRelease⟩ := Mma.electedCommitOccurs hp hX
      (PTX.Kernels.TmlFa4Fwd.Mma.releaseCommitSite 2) hVote (hLane.trans hLeader) (by omega)
    have hRelease' : Mma.ReleaseIssue X g (j + 1) .loopKey s := hRelease
    have hRank : Mma.releaseOccurrence X g (j + 1) .loopKey = phase := hRound
    obtain ⟨pos, score, hPrior, hPriorOrd, hBefore⟩ :=
      Scores.recurringScoreOfKeyRelease hp hX hRelease' oldStage
    have hOwner : g / l.block = cta := (Scores.scoreCommitActor hp hX hLater).1
    rw [hOwner] at hPrior hPriorOrd
    rw [hRank] at hPriorOrd
    have hSame := Scores.scoreCommitOrdinalInjective hp hX hOld hPrior
      (by dsimp [phase] at *; omega)
    refine ⟨start, hStart, fun step => ?_⟩
    obtain ⟨d, op, accum, predicates, hFrag, hR⟩ := hBank step
    have hBeforeFragment := hRelease'.beforeLaterCacheFragment hp hX
      (show X.MmaIssue (g, start + step.val) d op accum predicates from ⟨_, hFrag.decoded⟩)
      (by rw [hRank]; dsimp only [phase]; omega)
    exact ⟨d, op, accum, predicates, hFrag, hSame.1.symm ▸ hBefore.trans hBeforeFragment⟩

end PTX.Kernels.TmlFa4Fwd.Thread
