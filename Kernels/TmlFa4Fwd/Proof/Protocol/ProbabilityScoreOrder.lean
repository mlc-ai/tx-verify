-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityParity
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Scores

/-- Every preceding probability ordinal has a distinct physical poll before the score issue. -/
theorem probabilityObservedBeforeScoreOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta n : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X e cta stage spec rank) (packet : Fin 2)
    (hn : n < scoreCommitOrdinal l X cta stage e) :
    let log := X.objects (probabilityObject l cta stage packet)
    ∃ (k i phase : Nat) (r : Record Ref), log[i]? = some r ∧ r.id = .thread (e.1,k) ∧
      r.reply.waited = some true ∧ Resumes kernel X (e.1,k) e ∧
      observedAt log i = some phase ∧ n ≤ phase ∧
      k = MbarRing.Poll.nth X (probabilityObject l cta stage packet) e.1 n ∧
      n < okPolls (probabilityObject l cta stage packet) (X.tr e.1) := by
  obtain ⟨g,j⟩ := e
  let loc := probabilityObject l cta stage packet
  let log := X.objects loc
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none :=
    fun _ hr hs => actualInitOrPollClean hp hX hr (.inr hs)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨k, ev, q, acq, sc, hGet, hKind, hOrdinal, hResume⟩ :=
    scoreCommitProbabilityOfOrdinal hp hX hIssue packet hn
  obtain ⟨source, kind⟩ := ev
  change kind = _ at hKind
  subst kind
  have hNth := MbarRing.Poll.nth_eq hGet
  rw [hOrdinal] at hNth
  have hOrdinalLt : n < okPolls loc (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  obtain ⟨i, r, _, hr, hid, _, hSuccess, _, hBefore⟩ :=
    MbarRing.Poll.record hX hClean hOrdinalLt
  rw [hNth] at hid
  have hSel := objectThreadSelected_iff.mpr ⟨_, hid⟩
  have hChecked := X.objects_checked hX loc
  have hAlt := probabilitySelectedAlternates hp hX (g := g) (cta := cta) stage packet
  obtain ⟨s, hs, hLower, _⟩ :=
    hChecked.selected_poll_phase_ge hNo (objectThreadSelected g) (by decide) hAlt hr hSel hSuccess
  have hP : 0 < s.phase := by omega
  obtain ⟨st, q, hSt, _, _, hComplete⟩ := hChecked.okPoll hr hSuccess
  rw [hs] at hSt
  obtain rfl := Option.some.inj hSt
  have hPhase : observedAt log i = some (s.phase - 1) := by
    change (log[i]?).bind (·.reply.completed) = _
    rw [hr, Option.bind_some, hComplete, ite_eq_left hP]
  refine ⟨k, i, s.phase-1, r, hr, hid, hSuccess, hResume, hPhase, ?_, hNth.symm,hOrdinalLt⟩
  omega

/-- A recurring score issue follows a real successful probability observation of at least
the preceding score generation, separately for either packet of that physical stage. -/
theorem probabilityObservedBeforeScore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X e cta stage spec rank) (packet : Fin 2)
    (hPos : 0 < scoreCommitOrdinal l X cta stage e) :
    let log := X.objects (probabilityObject l cta stage packet)
    ∃ (k i phase : Nat) (r : Record Ref), log[i]? = some r ∧ r.id = .thread (e.1,k) ∧
      r.reply.waited = some true ∧ Resumes kernel X (e.1,k) e ∧
      observedAt log i = some phase ∧ scoreCommitOrdinal l X cta stage e ≤ phase + 1 := by
  let n := scoreCommitOrdinal l X cta stage e - 1
  have hN : n < scoreCommitOrdinal l X cta stage e := by dsimp [n]; omega
  obtain ⟨k,i,phase,r,hr,hId,hOk,hResume,hPhase,hBound,_,_⟩ :=
    probabilityObservedBeforeScoreOrdinal hp hX hIssue packet hN
  exact ⟨k,i,phase,r,hr,hId,hOk,hResume,hPhase,by dsimp [n] at hBound; omega⟩

/-- A softmax credit follows an actual score observation of at least its generation. -/
theorem scoreObservedBeforeSoftmaxCredit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta : Nat} (stage packet : Fin 2)
    (hw : Prologue.warpIndex l e.1 < 8) (hCredit : ProbabilityCredit l X e cta stage packet) :
    let log := X.objects (scoreReadyObject l cta stage)
    ∃ (k i phase : Nat) (r : Record Ref), log[i]? = some r ∧ r.id = .thread (e.1,k) ∧
      r.reply.waited = some true ∧ Resumes kernel X (e.1,k) e ∧
      observedAt log i = some phase ∧ probabilityOrdinal l X cta stage packet e ≤ phase := by
  obtain ⟨g,j⟩ := e
  let n := probabilityOrdinal l X cta stage packet (g,j)
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  obtain ⟨hCta, hRole⟩ := probabilityCreditRole hp hX stage packet hCredit
  have hStage : Prologue.warpIndex l g / 4 = stage.val := by
    rcases hRole with h | h
    · exact h.2
    · have hCorrection : 8 ≤ Prologue.warpIndex l g := h.2.1
      change Prologue.warpIndex l g < 8 at hw
      omega
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none :=
    fun _ hr hs => actualInitOrPollClean hp hX hr (.inr hs)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨k, ev, q, acq, sc, hGet, hKind, hOrdinal, hResume⟩ :=
    softmaxProbabilityCreditScorePoll hp hX stage packet hw hCredit
  obtain ⟨source, kind⟩ := ev
  change kind = _ at hKind
  subst kind
  have hNth := MbarRing.Poll.nth_eq hGet
  rw [hOrdinal] at hNth
  have hOrdinalLt : n < okPolls loc (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  obtain ⟨i, r, _, hr, hid, _, hSuccess, _, hBefore⟩ :=
    MbarRing.Poll.record hX hClean hOrdinalLt
  rw [hNth] at hid
  have hSel := objectThreadSelected_iff.mpr ⟨_, hid⟩
  have hChecked := X.objects_checked hX loc
  have hAlt := scoreReadySelectedAlternates hp hX stage hw hCta hStage
  obtain ⟨s, hs, hLower, _⟩ :=
    hChecked.selected_poll_phase_ge hNo (objectThreadSelected g) (by decide) hAlt hr hSel hSuccess
  have hP : 0 < s.phase := by omega
  obtain ⟨st, q, hSt, _, _, hComplete⟩ := hChecked.okPoll hr hSuccess
  rw [hs] at hSt
  obtain rfl := Option.some.inj hSt
  have hPhase : observedAt log i = some (s.phase - 1) := by
    change (log[i]?).bind (·.reply.completed) = _
    rw [hr, Option.bind_some, hComplete, ite_eq_left hP]
  refine ⟨k, i, s.phase-1, r, hr, hid, hSuccess, hResume, hPhase, ?_⟩
  change n ≤ s.phase - 1
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
