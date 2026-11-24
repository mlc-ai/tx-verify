-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCohortIteration
public import Kernels.TmlFa4Fwd.Proof.Progress.Async
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderEmptyFaults
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCohortIteration
import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier PTX.AsyncCopy Prologue Epilogue
open Mma (SteadyRetirementAges RetiredCacheUse readyStage commitSpec)
open Thread.Mma (ReleaseForm ReleaseMatch EmptyReleaseAt atPrefix)
open Thread.Mma.Observation (emptyObject)
open Thread.Scores (ScoreCommit scoreCommitOrdinal)

/-- Maximality delivers an actual returned cache slot at its own physical
generation. The resulting history record is ready for loader reuse. -/
theorem deliveredRecurringCacheRetirement {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g use : Nat} {form : ReleaseForm}
    (hRetirement : RetiredCacheUse l X g use form) :
    ∃ issuer k, ∃ a : EmptyReleaseAt l X (emptyObject l g (readyStage use)) issuer k,
      SameWarp l g issuer ∧ a.form = form ∧ a.ordinal = use/3 ∧ a.record.fault = none := by
  obtain ⟨issuer,idx,hSame,hIssue,paired,hSlot,hOrdinal⟩ := hRetirement
  let spec := commitSpec l issuer (l.sharedBase+8*(readyStage use).val+56)
  let loc := emptyObject l g (readyStage use)
  have hCta : issuer/l.block = g/l.block := hSame.1.2.2.symm
  have hh : emptyObject l issuer (readyStage use) = loc := by
    simp only [loc,emptyObject,hCta]
  have hTarget : TcCommit.target spec 0 = some loc :=
    (Mma.recurringRetirementTarget l issuer use).trans (congrArg some hh)
  have hCommit : X.Commit (issuer,idx) spec := ⟨_,hIssue⟩
  have hArrive := (mmaAndCommitsDrained hp hMax hFrame).2 _ _ 0 loc hCommit hTarget
  obtain ⟨tag,he⟩ := hCommit
  have hAction : objectAction X X.async loc (.async (issuer,idx) (.tcNotify 0)) =
      some (.arrive 1 0) := by simp [objectAction,he,hTarget,hArrive]
  obtain ⟨k,r,hAt,hId,_⟩ := MbarOneShot.Hist.record_of_action hMax.1 hAction
  let a : EmptyReleaseAt l X loc issuer k :=
    ⟨r,hAt,idx,0,form,spec,hId,hIssue,hTarget,hh ▸ paired⟩
  refine ⟨issuer,k,a,hSame,rfl,?_,?_⟩
  · have hTransport {target : Loc} (heq : emptyObject l issuer (readyStage use) = target) :
        let next : ReleaseMatch l X issuer idx form target := heq ▸ paired
        (atPrefix l X issuer next.wait).kvAcquires next.slot = use/3 := by
      cases heq
      exact hOrdinal
    exact hTransport hh
  · exact Protocol.LoaderReady.emptyHistoryClean hp hMax.1 g (readyStage use)
      (List.mem_of_getElem? hAt)

/-- The new recurring score commit is delivered at its exact CTA/stage generation. -/
theorem deliveredRecurringScore {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g visit : Nat} (hAge : SteadyRetirementAges l X g visit)
    (stage : Fin 2) :
    ∃ issue spec, issue.1/l.block = g/l.block ∧
      ScoreCommit l X issue (g/l.block) stage spec 0 ∧
      scoreCommitOrdinal l X (g/l.block) stage issue = visit+1 ∧
      (0 : Fin 16) ∈ X.tcNotified issue := by
  obtain ⟨issuer,idx,hw,_,_,hScores⟩ := hAge.keyAndScores
  obtain ⟨score,spec,hs,hRank,_⟩ := hScores stage
  have hCta : issuer/l.block = g/l.block := hw.1.2.2.symm
  have hDelivery := (mmaAndCommitsDrained hp hMax hFrame).2 _ _ 0 _ hs.1 hs.2
  refine ⟨(issuer,score),spec,hCta,?_,?_,hDelivery⟩
  · rwa [hCta] at hs
  · rwa [hCta] at hRank

end PTX.Kernels.TmlFa4Fwd.Progress
