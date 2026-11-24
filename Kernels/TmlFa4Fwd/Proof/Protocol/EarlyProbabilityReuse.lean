-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityStoreScoreOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
import Lemmas.Protocol.UnitHandoff
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.TcMma PTX.AsyncCopy Thread Thread.Scores Prologue

/-- A later score fragment observes a joint generation containing the actual lane's
credit for this early probability store or a successor visit on the same lane. -/
theorem earlyProbabilityStoreBeforeLaterQk {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hGuard : CorrectionJointGuards l X)
    {mma store wait : EvId} (stage : Fin 2) {cell : Cell}
    (hStore : EarlyProbabilityStore X store)
    (hFoot : TensorStoreFootprint l store cell (.probability stage))
    {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hMma : X.MmaIssue mma d op acc mask) (hSame : SameCta l mma.1 store.1)
    (hSeen : ProbabilityStoreScore l X store stage) (hLater : hSeen.commit.2 ≤ mma.2)
    (hAcquire : MmaProbabilityAcquire l X mma stage 0 wait) :
    StoreDoneBefore l X store mma := by
  let cta := store.1/l.block
  let object := probabilityObject l cta stage 0
  have hCta := hSame.2.2
  have hGroup : warpIndex l store.1 / 4 = stage.val := by
    have h := hFoot.warpGroup
    change (store.1%l.block)/128 = stage.val at h
    unfold warpIndex
    omega
  have hSupply := hStore.scoreUses hp hX stage hGroup
  have hScore := scoreCommitCountBeforeMma hp hX hMma hSeen.score hCta hLater
  obtain ⟨i,phase,poll,hPoll,hId,hSuccess,hPhase,hBudget⟩ := hAcquire.record hp hX
  rw [hCta] at hPoll hPhase hBudget
  have hOrd := hSeen.coversCursor
  change probabilityOrdinal l X cta stage 0 store + 1 ≤
    okPolls (scoreReadyObject l cta stage) ((X.tr store.1).take store.2) at hSupply
  change okPolls (scoreReadyObject l cta stage) ((X.tr store.1).take store.2) ≤
    scoreCommitOrdinal l X cta stage hSeen.commit + 1 at hOrd
  change scoreCommitOrdinal l X cta stage hSeen.commit + 1 ≤
    scoreCommitOrdinal l X cta stage mma at hScore
  change scoreCommitOrdinal l X cta stage mma ≤ phase+1 at hBudget
  have hWithin : probabilityOrdinal l X cta stage 0 store ≤ phase := by omega
  have hw : warpIndex l store.1 < 8 := by have := stage.isLt; omega
  obtain ⟨credit,hCredit,hLane,hGeneration,hObserve⟩ :=
    jointPollObservesLane hp hX hGuard stage rfl hw hGroup hPoll hSuccess hPhase
  have hBefore := hStore.beforeCredit hCredit hLane (hGeneration.symm ▸ hWithin)
  have hAcquire' : ScoreAcquire X wait object := by
    obtain ⟨e,q,he,hKind⟩ := hAcquire.event
    rw [hCta] at hKind
    exact ⟨e,q,he,hKind⟩
  rw [hId] at hObserve
  have hNotify := hAcquire'.observes hObserve
  have hWaitCta : SameCta l credit.1 wait.1 := by
    rw [hLane,hAcquire.resume.1.1]
    exact ⟨hSame.2.1,hSame.1,hCta.symm⟩
  have hRelease : MbarRelease X credit object .cta := ⟨0,1,hCredit⟩
  have hHandoff := Staging.baseCausality_of_handoff (e := credit) hRelease hNotify
    (MbarRing.Unit.Gate.scopesMeet hWaitCta .cta .cta) ⟨rfl,le_rfl⟩ hAcquire.resume.1
  exact earlyProbabilityDoneThroughCredit hp hX stage hStore hCredit hBefore hHandoff

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
