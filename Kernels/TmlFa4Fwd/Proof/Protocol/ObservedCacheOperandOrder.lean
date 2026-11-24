-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheOperandElements
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyFiniteOperands
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedByteRange
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreLoadGeneration
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedQkBank
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Lemmas.Async.AsyncChain
import Lemmas.Execution.MemoryPresence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)
open Thread.Loader (CachePlane)

private theorem cacheCopyOrderOfAcquiredSlot {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j wait use d index : Nat} {block : Fin 4} {step : Fin 8} {plane : CachePlane}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hDone : Completed l X (g,wait) (kvUseStage use) (use/3))
    (hMma : X.MmaIssue (g,j) d op accum mask) (hBefore : TraceBefore X (g,wait) (g,j))
    {loc : Loc} (hLoc : op.byteLoc .b index = some loc)
    (hBytes : op.byteLoc .b index = (cacheOperand l g block step use plane).byteLoc .b index)
    {copy : EvId} {s : Spec} (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc)
    (hRival : ∀ pub (group : Thread.Loader.PublishedCopyGroup l X pub) k spec,
      X.AsyncArrive pub (Thread.Loader.readyObject l g (kvUseStage use)) true →
      generation l X pub (kvUseStage use) = use/3 →
      (k,spec) ∈ group.copies → spec.dst.Covers loc →
      copy = (pub.1,k) ∨
      modelCausality l X loc (.async copy (.write .copy)) (.async (pub.1,k) (.write .copy)) ∨
      modelCausality l X loc (.async (g,j) (.mmaRead true index)) (.async copy (.write .copy))) :
    ByteCausality l X loc (.async copy (.write .copy)) (.async (g,j) (.mmaRead true index)) ∨
      ByteCausality l X loc (.async (g,j) (.mmaRead true index)) (.async copy (.write .copy)) := by
  have hNorm := hBytes.symm.trans hLoc
  obtain ⟨row,k,b,hr,hk,hInd⟩ := cacheOperandFlatByteCoordinates hNorm
  have hB := b.isLt
  obtain ⟨lane,pair,upper,word,hWord,hVector⟩ :=
    cacheOperandWordVector hp g block step use plane hr hk
  have hAt := Option.some.inj ((hInd ▸ hNorm).symm.trans (hVector b))
  have hOff : 2 * word + b.val < 16 := by omega
  have hPublication :=
    hDone.actualOperandCoveringCopyWithPublication hp hX (isB := true) lane pair upper hOff
      hMma hBefore hLoc hAt
  obtain ⟨pub, group, chosen, spec, _, hPub, _, hPhase, _, _, hMember, _, hChosen,
    hWritten, hUse⟩ :=
    hPublication
  rcases hRival pub group chosen spec hPub hPhase hMember hChosen with hSame | hEarly | hLate
  · exact .inl (.direct (hSame.symm ▸ hUse))
  · have hRange := mmaSharedByteRange hp hX (isB := true) (.inl ⟨d,op,accum,mask,hMma,hLoc⟩)
    obtain ⟨hThread,_,_,_,hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
    have hCopyOwner : loc.cta = copy.1 / l.block := by rw [hDst] at hCover; exact hCover.2.1
    obtain ⟨_,he⟩ := hMma
    have hCta : SameCta l copy.1 g :=
      ⟨hThread, event_thread_lt hX he, hCopyOwner.symm.trans hRange.cta⟩
    exact .inl (.direct (modelCausality_async_trans hEarly hWritten.present hUse (.inl hCta)))
  · exact .inr (.direct hLate)

/-- Any cache copy covering an actual MMA B operand byte is ordered before or
after the read. The governing acquire supplies the serving vector, and the
empty-slot handoff orders copies that overwrite it. -/
theorem cacheCopyOrderedWithObservedOperand {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j d index : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue (g,j) d op accum mask) {loc : Loc} (hLoc : op.byteLoc .b index = some loc)
    {copy : EvId} {s : Spec} (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.async (g,j) (.mmaRead true index)) ∨
      ByteCausality l X loc (.async (g,j) (.mmaRead true index)) (.async copy (.write .copy)) := by
  rcases actualMmaInstruction hX hMma with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · let stage := qkStage block
    by_cases hOpening : block.val < 2
    · have hBlock : block = initialQkBlock stage := Fin.ext (by
        change block.val = block.val % 2
        omega)
      have hQ : QkInstruction X (g,j) (initialQkBlock stage) step d op accum mask := hBlock ▸ hQk
      have hInit := hQ.initialQueryFragment
      obtain ⟨wait,hPoll,hEarlier,hOrdinal⟩ := hInit.keyReadyInPrefix hp hX
      have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hMma).1
      obtain ⟨done⟩ := completedForObservedIssuer hp hX hWarp
        (Thread.Mma.sameCacheReleaseIssuer hp hX hMma) hPoll (actualEmptyGuardLower hp hX g 0)
      rw [hOrdinal] at done
      have hBytes : op.byteLoc .b index =
          (cacheOperand l g (initialQkBlock stage) step 0 .key).byteLoc .b index := by
        rw [hQ.operandsOfKey hp hX (hQ.initialKeyOperand hp hX stage)]
        rfl
      apply cacheCopyOrderOfAcquiredSlot hp hX done hMma hEarlier hLoc hBytes hCopy hCover
      intro pub group k spec hPub hPhase hMember hChosen
      exact (initialKeyCopyCompetitors hp hX hInit hMma hPub hPhase hMember hLoc hChosen
        copy s hCopy hCover).imp_right Or.inr
    · have hBlock : block = recurringKeyBlock stage := Fin.ext (by
        have := block.isLt
        change block.val = block.val%2+2
        omega)
      have hQ : QkInstruction X (g,j) (recurringKeyBlock stage) step d op accum mask := hBlock ▸ hQk
      obtain ⟨wait,use,⟨done⟩,hEarlier,hRank,hBytes⟩ :=
        recurringKeyFragmentReadyBytesExact hp hX stage hQ
      apply cacheCopyOrderOfAcquiredSlot hp hX done hMma hEarlier hLoc (hBytes index) hCopy hCover
      intro pub group k spec hPub hPhase hMember hChosen
      exact recurringKeyCopyCompetitors hp hX stage hQ hRank hPub hPhase hMember hLoc hChosen
        copy s hCopy hCover
  · obtain ⟨use,wait,hUse,⟨done⟩,hEarlier,hBytes⟩ := valueOperandReadyInPrefix hp hX hPv
    apply cacheCopyOrderOfAcquiredSlot hp hX done hMma hEarlier hLoc (hBytes index) hCopy hCover
    intro pub group k spec hPub hPhase hMember hChosen
    exact valueCopyCompetitors hp hX hPv hUse hPub hPhase hMember hLoc hChosen
      copy s hCopy hCover

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
