-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemTailProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityStoreScoreOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.TailProbabilityObservations
import Lemmas.Protocol.UnitHandoff
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.AsyncCopy Thread Thread.Scores Prologue

/-- A later QK's tail acquire observes the store warp's elected credit from its
current generation or later, after the matching ordinary store wait. -/
theorem tailProbabilityStoreBeforeLaterQk {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma store wait : EvId} (stage : Fin 2) {cell : Cell}
    (hStore : TailProbabilityStore X store)
    (hFoot : TensorStoreFootprint l store cell (.probability stage))
    {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hMma : X.MmaIssue mma d op acc mask) (hSame : SameCta l mma.1 store.1)
    (hSeen : ProbabilityStoreScore l X store stage) (hLater : hSeen.commit.2 ≤ mma.2)
    (hAcquire : MmaProbabilityAcquire l X mma stage 1 wait) :
    StoreDoneBefore l X store mma := by
  let cta := store.1/l.block
  let object := probabilityObject l cta stage 1
  let warp : Fin 4 := ⟨warpIndex l store.1 % 4,Nat.mod_lt _ (by decide)⟩
  have hCta := hSame.2.2
  have hGroup : warpIndex l store.1 / 4 = stage.val := by
    have h := hFoot.warpGroup
    change (store.1%l.block)/128 = stage.val at h
    unfold warpIndex
    omega
  have hSupply := tailProbabilityStoreScoreUses hp hX stage hStore hGroup
  have hScore := scoreCommitCountBeforeMma hp hX hMma hSeen.score hCta hLater
  obtain ⟨i,phase,poll,hPoll,hId,hSuccess,hPhase,hBudget⟩ := hAcquire.record hp hX
  rw [hCta] at hPoll hPhase hBudget
  have hOrd := hSeen.coversCursor
  change warpBars X store.1 store.2 + 1 ≤
    okPolls (scoreReadyObject l cta stage) ((X.tr store.1).take store.2) at hSupply
  change okPolls (scoreReadyObject l cta stage) ((X.tr store.1).take store.2) ≤
    scoreCommitOrdinal l X cta stage hSeen.commit + 1 at hOrd
  change scoreCommitOrdinal l X cta stage hSeen.commit + 1 ≤
    scoreCommitOrdinal l X cta stage mma at hScore
  change scoreCommitOrdinal l X cta stage mma ≤ phase+1 at hBudget
  have hWithin : warpBars X store.1 store.2 ≤ phase := by omega
  obtain ⟨credit,hCredit,hWarp,hGeneration,hObserve⟩ :=
    tailCreditOfObservedWarpExact hp hX stage warp hPoll hSuccess hPhase
  have hOwner := (probabilityCreditRole hp hX stage 1 hCredit).1
  have hCreditIn : credit.1 < l.threads := by
    obtain ⟨_,he⟩ := hCredit
    exact event_thread_lt hX he
  have hSameWarp : SameWarp l store.1 credit.1 := by
    refine ⟨⟨hSame.2.1,hCreditIn,hOwner.symm⟩,?_⟩
    change warpIndex l store.1 = warpIndex l credit.1
    rw [hWarp]
    dsimp only [warp]
    omega
  have hAcquire' : ScoreAcquire X wait object := by
    obtain ⟨e,q,he,hKind⟩ := hAcquire.event
    rw [hCta] at hKind
    exact ⟨e,q,he,hKind⟩
  rw [hId] at hObserve
  have hNotify := hAcquire'.observes hObserve
  have hWaitCta : SameCta l credit.1 wait.1 := by
    rw [hAcquire.resume.1.1]
    exact ⟨hCreditIn,hSame.1,hOwner.trans hCta.symm⟩
  have hRelease : MbarRelease X credit object .cta := ⟨0,1,hCredit⟩
  have hHandoff := Staging.baseCausality_of_handoff (e := credit) hRelease hNotify
    (MbarRing.Unit.Gate.scopesMeet hWaitCta .cta .cta) ⟨rfl,le_rfl⟩ hAcquire.resume.1
  exact tailProbabilityDoneThroughWarpCredit hp hX stage hStore hCredit hSameWarp
    (hGeneration.symm ▸ hWithin) hHandoff

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
