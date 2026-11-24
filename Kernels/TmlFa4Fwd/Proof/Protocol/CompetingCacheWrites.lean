-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PendingCacheOperandOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheCopyMatch
import Kernels.TmlFa4Fwd.Proof.Thread.SelectedCacheCopyUse
import Kernels.TmlFa4Fwd.Proof.Protocol.PrimingCacheWriteOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.InitialCacheOperandOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandWriterOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvUseStage_val)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem recurringCopyCompetitors {mma pub : EvId} {use byte j : Nat} {loc : Loc}
    {spec : Spec} {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l mma.1 (kvUseStage use)) true)
    (hPhase : generation l X pub (kvUseStage use) = use/3) (hUse : 2 ≤ use)
    (hMember : (j,spec) ∈ group.copies) (hCover : spec.dst.Covers loc)
    (hLater : ∀ (other : EvId) (copy : Spec) (event : Event), X.get other = some event →
      Thread.Loader.recurringVectorEvent event → event.kind = .copy copy → copy.dst.Covers loc →
      use < Thread.Loader.recurringUseBefore X other →
      modelCausality l X loc (.async mma (.mmaRead true byte)) (.async other (.write .copy))) :
    ∀ other copy, X.Copy other copy → copy.dst.Covers loc →
      other = (pub.1,j) ∨
      modelCausality l X loc (.async other (.write .copy)) (.async (pub.1,j) (.write .copy)) ∨
      modelCausality l X loc (.async mma (.mmaRead true byte)) (.async other (.write .copy)) := by
  intro other copy hCopy hOther
  obtain ⟨hChosenRank,chosen,hGet,hChosen,hSpec⟩ :=
    group.recurringMemberAtUse hp hX hPub hPhase hUse hMember
  rcases Thread.Loader.copyPrimingOrRecurringVector hX hCopy with hK | hV | hRepeat
  · obtain ⟨pair,upper,hPriming⟩ := hK
    exact .inr (.inl (primingCopyBeforeRecurringCopy hp hX hPriming.primingCacheVector hGet
      hChosen hSpec hOther hCover))
  · obtain ⟨pair,upper,hPriming⟩ := hV
    exact .inr (.inl (primingCopyBeforeRecurringCopy hp hX hPriming.primingCacheVector hGet
      hChosen hSpec hOther hCover))
  obtain ⟨event,he,hVector,hKind⟩ := hRepeat
  rcases lt_trichotomy (Thread.Loader.recurringUseBefore X other) use with hLt | hEq | hGt
  · exact .inr (.inl (recurringCopyBeforeLaterRecurringCopy hp hX he hGet
      hVector hChosen hKind hSpec hOther hCover (hChosenRank.symm ▸ hLt)))
  · have hRank : 3 * generation l X pub (kvUseStage use) + (kvUseStage use).val = use := by
      rw [hPhase, kvUseStage_val]
      omega
    obtain ⟨producer,index⟩ := other
    exact .inl (overlappingRecurringCopyOfSameUse hp hX he hVector hKind hPub
      (hEq.trans hRank.symm) group hMember hCover hOther)
  · exact .inr (.inr (hLater other copy event he hVector hKind hOther hGt))

/-- An overlapping copy is the selected recurring K writer, precedes that
writer, or follows the actual QK operand read. -/
theorem recurringKeyCopyCompetitors (stage : Fin 2) {g index : Nat} {step : Fin 8} {d : Nat}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
    {use byte j : Nat} {pub : EvId} {loc : Loc} {spec : Spec}
    {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hUse : use = (Thread.Mma.atPrefix l X g index).kvAcquires 0 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 1 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 2 - 1)
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l g (kvUseStage use)) true)
    (hPhase : generation l X pub (kvUseStage use) = use/3) (hMember : (j,spec) ∈ group.copies)
    (hByte : op.byteLoc .b byte = some loc) (hCover : spec.dst.Covers loc) :
    ∀ other copy, X.Copy other copy → copy.dst.Covers loc →
      other = (pub.1,j) ∨
      modelCausality l X loc (.async other (.write .copy)) (.async (pub.1,j) (.write .copy)) ∨
      modelCausality l X loc (.async (g,index) (.mmaRead true byte))
        (.async other (.write .copy)) := by
  obtain ⟨_,actual,_,_,hActual,hLoc⟩ := recurringKeyFragmentReadyBytesExact hp hX stage hKey
  obtain rfl : use = actual := hUse.trans hActual.symm
  obtain ⟨row,k,b,hr,hk,rfl⟩ := cacheOperandFlatByteCoordinates
    ((hLoc byte).symm.trans hByte)
  have hPositive := (hKey.recurringKeyOperandOfPositiveEvenReadyUse hp hX stage).2.2
  have hRecurring : 2 ≤ use := hActual.symm ▸ hPositive
  apply recurringCopyCompetitors hp hX hPub hPhase hRecurring hMember hCover
  rintro ⟨producer,copyIndex⟩ copy event he hVector hKind hOther hLater
  exact (recurringKeyBeforeLaterCoveringCopy hp hX stage hKey he hVector hKind hActual
    hr hk b hByte hOther hLater).2

/-- An overlapping copy is the selected recurring V writer, precedes that
writer, or follows the actual PV operand read. -/
theorem recurringValueCopyCompetitors {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,index) block step d op accum mask) {use byte j : Nat} {pub : EvId}
    {loc : Loc} {spec : Spec} {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hUse : Thread.Mma.LatestValueReadyUse l X g index use) (hRecurring : 2 ≤ use)
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l g (kvUseStage use)) true)
    (hPhase : generation l X pub (kvUseStage use) = use/3) (hMember : (j,spec) ∈ group.copies)
    (hByte : op.byteLoc .b byte = some loc) (hCover : spec.dst.Covers loc) :
    ∀ other copy, X.Copy other copy → copy.dst.Covers loc →
      other = (pub.1,j) ∨
      modelCausality l X loc (.async other (.write .copy)) (.async (pub.1,j) (.write .copy)) ∨
      modelCausality l X loc (.async (g,index) (.mmaRead true byte))
        (.async other (.write .copy)) := by
  apply recurringCopyCompetitors hp hX hPub hPhase hRecurring hMember hCover
  intro other copy event he hVector hKind hOther hLater
  exact valueReadBeforeFutureCoveringVector hp hX hValue hUse hByte
    he hVector hKind hOther hLater

/-- The actual V ready use orders competing copies for both priming and recurring PV. -/
theorem valueCopyCompetitors {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,index) block step d op accum mask) {use byte j : Nat} {pub : EvId}
    {loc : Loc} {spec : Spec} {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hUse : Thread.Mma.LatestValueReadyUse l X g index use)
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l g (kvUseStage use)) true)
    (hPhase : generation l X pub (kvUseStage use) = use/3) (hMember : (j,spec) ∈ group.copies)
    (hByte : op.byteLoc .b byte = some loc) (hCover : spec.dst.Covers loc) :
    ∀ other copy, X.Copy other copy → copy.dst.Covers loc →
      other = (pub.1,j) ∨
      modelCausality l X loc (.async other (.write .copy)) (.async (pub.1,j) (.write .copy)) ∨
      modelCausality l X loc (.async (g,index) (.mmaRead true byte))
        (.async other (.write .copy)) := by
  rcases Nat.eq_or_lt_of_le (show 1 ≤ use from by
    obtain ⟨_,_,_,hOdd,_,_⟩ := hUse
    omega) with rfl | hRepeat
  · intro other copy hCopy hOverlap
    exact (initialValueCopyCompetitors hp hX hValue hUse hPub hPhase hMember hByte hCover
      other copy hCopy hOverlap).elim .inl (.inr ∘ .inr)
  · exact recurringValueCopyCompetitors hp hX hValue hUse hRepeat hPub hPhase hMember hByte hCover

/-- Every writer overlapping an actual recurring K operand byte is the serving
writer, precedes it, or follows the operand read. -/
theorem recurringKeyOperandWriterOrder (stage : Fin 2) {g index : Nat} {step : Fin 8} {d : Nat}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
    {use byte j : Nat} {pub : EvId} {loc : Loc} {spec : Spec}
    {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hUse : use = (Thread.Mma.atPrefix l X g index).kvAcquires 0 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 1 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 2 - 1)
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l g (kvUseStage use)) true)
    (hPhase : generation l X pub (kvUseStage use) = use/3) (hMember : (j,spec) ∈ group.copies)
    (hByte : op.byteLoc .b byte = some loc) (hSource : spec.dst.Covers loc) {other : Ref} {a : Acc}
    {data : List Byte} (hWrite : X.MemWrites other a data) (hCover : a.Covers loc) :
    other = .async (pub.1,j) (.write .copy) ∨
      modelCausality l X loc other (.async (pub.1,j) (.write .copy)) ∨
      modelCausality l X loc (.async (g,index) (.mmaRead true byte)) other :=
  cacheOperandOrderOfCopyOrder hp hX ⟨_,hKey.decoded⟩ hByte
    (recurringKeyCopyCompetitors hp hX stage hKey hUse hPub hPhase hMember hByte hSource)
    hWrite hCover

/-- Every writer overlapping an actual V operand byte is the serving writer,
precedes it, or follows its PV operand read. -/
theorem valueOperandWriterOrder {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,index) block step d op accum mask) {use byte j : Nat} {pub : EvId}
    {loc : Loc} {spec : Spec} {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hUse : Thread.Mma.LatestValueReadyUse l X g index use)
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l g (kvUseStage use)) true)
    (hPhase : generation l X pub (kvUseStage use) = use/3) (hMember : (j,spec) ∈ group.copies)
    (hByte : op.byteLoc .b byte = some loc) (hSource : spec.dst.Covers loc) {other : Ref} {a : Acc}
    {data : List Byte} (hWrite : X.MemWrites other a data) (hCover : a.Covers loc) :
    other = .async (pub.1,j) (.write .copy) ∨
      modelCausality l X loc other (.async (pub.1,j) (.write .copy)) ∨
      modelCausality l X loc (.async (g,index) (.mmaRead true byte)) other :=
  cacheOperandOrderOfCopyOrder hp hX ⟨_,hValue.decoded⟩ hByte
    (valueCopyCompetitors hp hX hValue hUse hPub hPhase hMember hByte hSource) hWrite hCover

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
