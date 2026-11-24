-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOutputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Lemmas.Kernel.ExitChain
import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.AsyncCopy PTX.Proof Prologue

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem outputCommitTracksMma {mma commit : EvId} {dst : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} {spec : TcCommit.Spec}
    (hIssue : X.MmaIssue mma dst op accum mask) (hCommit : SecondOutputCommit X commit spec)
    (hCta : mma.1 / l.block = commit.1 / l.block) : TracksMma X mma commit := by
  obtain ⟨hWarp, _, _, _, _, he, hLeader⟩ := mmaIssueElection hp hX hIssue
  obtain ⟨site, hIssueGet⟩ := hIssue
  have hSameWarp : SameWarp l mma.1 commit.1 :=
    ⟨⟨event_thread_lt hX hIssueGet, event_thread_lt hX hCommit.decoded, hCta⟩,
      hWarp.trans (hCommit.issuerWarp hp hX).symm⟩
  obtain ⟨_, _, _, hc, hCommitLeader⟩ :=
    TmlFa4Fwd.Mma.secondOutputCommitLeader hp hX hCommit.decoded
  have hLane := selected_elect_thread_unique hX.elect he hc hSameWarp hLeader hCommitLeader
  have hEarlier := (mmaBeforeSecondOutputCommit hX ⟨site, hIssueGet⟩ hCommit hLane).2.1
  exact ⟨hLane, hEarlier, .inl ⟨_, _, _, _, ⟨site, hIssueGet⟩⟩, _, hCommit.issued⟩

/-- The terminal output acquire observes every MMA tracked by its commit before the
correction lane's output load and the CTA's collective Tensor Memory release. -/
theorem mmaCompletedBeforeReleaseOfOutputLoad {mma i d : EvId} {dst address : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {chunk : Fin 16} {values : List Value}
    {shape : TcShape} (hIssue : X.MmaIssue mma dst op accum mask)
    (hLoad : X.get i = some
      ⟨TmlFa4Fwd.Correction.finalizeLoadPc 1 chunk, .tc (.ld address values shape)⟩)
    (hMmaCta : mma.1 / l.block = i.1 / l.block) (hCta : i.1 / l.block = d.1 / l.block)
    (hRelease : Deallocation X d) :
    TcMma.DoneBefore l X mma d := by
  obtain ⟨wait, hWait, hPo⟩ := Correction.secondAcquireBeforeFinalizationLoad hp hX hLoad
  obtain ⟨commit, spec, rank, scope, hCommit, hLocal, hTarget, hNotify, hObserve⟩ :=
    secondOutputAcquireCommit hp hX hWait
  have hLocalLoad : SameCta l commit.1 i.1 := hPo.1 ▸ hLocal
  have hTrack := outputCommitTracksMma hp hX hIssue hCommit (hMmaCta.trans hLocalLoad.2.2.symm)
  have hObserved : AsyncObserved X mma .mmaDone wait true scope :=
    ⟨.async commit (.tcNotify rank), _, ⟨commit, spec, rank, rfl, hTrack, hCommit.issued,
      hTarget, hNotify⟩, hObserve⟩
  have hLoadData : TensorDataEvent X i := ⟨_, hLoad, .inl rfl⟩
  have hBeforeLoad : baseCausality l X wait i := .single (.inl hPo)
  exact .inl ⟨wait, scope, hObserved,
    MbarRing.Unit.Gate.scopesMeet (hTrack.1.symm ▸ hLocal) .cluster scope,
    hBeforeLoad.trans (tensorDataBeforeDeallocation hp hX hCta hLoadData hRelease)⟩

/-- Release in a scheduled CTA follows every MMA, through the correction role's output acquire. -/
theorem mmaCompletedBeforeReleaseOfWork {mma d : EvId} {dst : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hIssue : X.MmaIssue mma dst op accum mask)
    (hWork : mma.1 / l.block < tilePrefix p p.batch * p.heads)
    (hCta : mma.1 / l.block = d.1 / l.block) (hRelease : Deallocation X d) :
    TcMma.DoneBefore l X mma d := by
  let g := (mma.1 / l.block) * l.block + 256
  have hOwner : g / l.block = mma.1 / l.block := by
    unfold g
    rw [hp.block]
    omega
  have hg : g < l.threads := by
    obtain ⟨_, he⟩ := hIssue
    have hGrid := NamedBar.cta_lt (event_thread_lt hX he)
    change (mma.1 / l.block) * l.block + 256 < l.grid * l.block
    rw [hp.block] at hGrid ⊢
    omega
  have hWarp : warpIndex l g = 8 := by
    unfold warpIndex g
    rw [hp.block]
    omega
  obtain ⟨j, mode, hArrival, _⟩ :=
    finalAllocationMemberBeforeDeallocation hp hX hg (by omega) (hOwner.trans hCta) hRelease
  have he := hArrival.correctionDecoded hp hX (hWarp.symm ▸ Nat.le_refl 8) (by omega)
  obtain ⟨i, _, _, hLoad⟩ :=
    correctionFinalOutputLoadOfActiveTail hp hX (g := g) (by omega) (by omega)
      (hOwner.symm ▸ hWork) he
  exact mmaCompletedBeforeReleaseOfOutputLoad hp hX hIssue hLoad hOwner.symm
    (hOwner.trans hCta) hRelease

/-- In an exited CTA with scheduled work, the correction role observes every issued MMA's
completion before its own exit. -/
theorem mmaFinishedAtExitOfWork {mma : EvId} {dst : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hIssue : X.MmaIssue mma dst op accum mask)
    (hWork : mma.1 / l.block < tilePrefix p p.batch * p.heads)
    (hExit : CtaExited l X (mma.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async mma .mmaDone) (mma.1 / l.block) := by
  have hGrid : mma.1 / l.block < l.grid := by
    obtain ⟨_, he⟩ := hIssue
    exact NamedBar.cta_lt (event_thread_lt hX he)
  obtain ⟨commit, spec, rank, wait, scope, finish, hCommit, hOwner, hTarget, hNotify,
    hObserve, hResumes, hFinish⟩ := terminalOutputObservedBeforeExit hp hX hGrid hWork hExit
  have hTrack := outputCommitTracksMma hp hX hIssue hCommit hOwner.symm
  have hObserved : AsyncObserved X mma .mmaDone wait true scope :=
    ⟨.async commit (.tcNotify rank), _, ⟨commit, spec, rank, rfl, hTrack, hCommit.issued,
      hTarget, hNotify⟩, hObserve⟩
  obtain ⟨hDone, hCompleted⟩ :=
    CompletedBefore.of_observesMma (A := Assumptions.all) hX.tcCommit hObserved
      (.single (DepStep.of_resumes l hResumes))
  exact SharedFinished.of_completedBefore hDone hFinish hCompleted
end

/-- Any release of a recorded allocation is a deallocation in the allocating CTA. -/
theorem allocationReleaseInOwnerCta {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} {r : Tmem.Pair.Requests}
    (hr : r ∈ X.tmemHistory cta) {d : EvId} (hRelease : Tmem.Pair.ReleaseOf l X r d) :
    d.1 / l.block = r.own.cta ∧ Deallocation X d := by
  rcases hRelease with hOwn | ⟨q,hq,_,_,_,_⟩
  · obtain ⟨_, _, _, _, ⟨group,he⟩, hLane | ⟨hCta,_⟩⟩ := hOwn
    · obtain ⟨lane,hd,_,_⟩ := hLane
      have hWarp := ((hX.tmemPair.1 cta).1 r hr).2.2.2.1
      have hBelow : r.own.warp * 32 + lane.val < l.block := by have := lane.isLt; omega
      have hPos := Nat.zero_lt_of_lt hBelow
      refine ⟨?_,Deallocation.of_decoded he⟩
      rw [hd]
      change (r.own.cta * l.block + r.own.warp * 32 + lane.val) / l.block = r.own.cta
      rw [Nat.add_assoc, Nat.mul_comm r.own.cta l.block, Nat.mul_add_div hPos,
        Nat.div_eq_of_lt hBelow, Nat.add_zero]
    · exact ⟨hCta,Deallocation.of_decoded he⟩
  · have hValid := (hX.tmemPair.2.1 q hq).1.2.1
    exact CtaGroup.noConfusion (TmlFa4Fwd.Mma.actualResourceRequest hX (hValid.2.2.1 0)).1

end PTX.Kernels.TmlFa4Fwd.Thread
