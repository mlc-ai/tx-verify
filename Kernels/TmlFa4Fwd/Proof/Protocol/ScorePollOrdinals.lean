-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.ScorePollOrdinal
import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityScoreOrder
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Order.WaitOrderObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Prologue Thread.Scores

/-- An observed same-stage score generation equals the lane's successful-poll ordinal.
A later commit needs a joint probability generation containing this lane's credit,
which cannot be published until the very score wait has returned. -/
theorem scorePollObservesExactCommit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hGuard : CorrectionJointGuards l X) {g cta n : Nat} (stage : Fin 2)
    (hOwner : g/l.block = cta) (hw : warpIndex l g < 8) (hStage : warpIndex l g/4 = stage.val)
    (hn : n < okPolls (scoreReadyObject l cta stage) (X.tr g)) :
    let loc := scoreReadyObject l cta stage
    let wait := (g,MbarRing.Poll.nth X loc g n)
    ∃ commit spec rank, ScoreCommit l X commit cta stage spec rank ∧
      scoreCommitOrdinal l X cta stage commit = n ∧
      MbarObserved X (.async commit (.tcNotify rank)) (.thread wait) := by
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  let wait := (g,MbarRing.Poll.nth X loc g n)
  have hChecked := X.objects_checked hX loc
  have hClean : ∀ r ∈ log, (∃ q success, r.action = .pollParity q success) → r.fault = none :=
    fun _ hr hP => actualInitOrPollClean hp hX hr (.inr hP)
  obtain ⟨i,poll,_,hRec,hId,_,hOk,_,hOrd⟩ := MbarRing.Poll.record hX hClean hn
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hAlt := scoreReadySelectedAlternates hp hX stage hw hOwner hStage
  have hSel := objectThreadSelected_iff.mpr ⟨_,hId⟩
  obtain ⟨st,hSt,hLower,_⟩ :=
    hChecked.selected_poll_phase_ge hNo (objectThreadSelected g) (by decide) hAlt hRec hSel hOk
  let phase := st.phase-1
  have hBound : n ≤ phase := by
    change n ≤ st.phase-1
    omega
  obtain ⟨_,_,hState,_,_,hCompleted⟩ := hChecked.okPoll hRec hOk
  rw [hSt] at hState
  obtain rfl := Option.some.inj hState
  have hPos : 0 < st.phase := by omega
  have hObserved : observedAt log i = some phase := by
    change log[i]? = some poll at hRec
    simp only [observedAt,hRec,Option.bind_some,hCompleted,ite_eq_left hPos,phase]
  obtain ⟨commit,spec,rank,hCommit,hGeneration,hNotify⟩ :=
    scoreCommitOfObservation hp hX stage hRec hOk hObserved
  rw [hId] at hNotify
  refine ⟨commit,spec,rank,hCommit,hGeneration.trans ?_,hNotify⟩
  by_contra! hWrong
  have hLater : n < scoreCommitOrdinal l X cta stage commit := by omega
  obtain ⟨prior,j,q,record,hR,hRid,hSuccess,hResume,hPhase,hQ,_,_⟩ :=
    probabilityObservedBeforeScoreOrdinal hp hX hCommit 0 hLater
  obtain ⟨credit,hC,hLane,hOrdinal,hCredit⟩ :=
    jointPollObservesLane hp hX hGuard stage hOwner hw hStage hR hSuccess hPhase
  rcases credit with ⟨lane,step⟩
  change lane = g at hLane
  subst lane
  have hPrior := scorePollResumesCreditOfLe hp hX stage 0 hw hC (hOrdinal.symm ▸ hQ)
  rw [hRid] at hCredit
  obtain ⟨_,hGet⟩ := hCommit.1
  have hIssue : DepStep l kernel X (.thread commit,false) (.async commit (.tcNotify rank),false) :=
    DepStep.issue ⟨_,hGet⟩ hNotify.1 (by intro _ h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  have hCycle := ((((Relation.TransGen.single (DepStep.of_resumes l hPrior)).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hCredit))).tail
    (DepStep.of_resumes l hResume)).tail hIssue).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hNotify))
  exact hX.depAcyclic _ hCycle

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
