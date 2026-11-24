-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.MbarRead
public import Kernels.TmlFa4Fwd.Proof.Protocol.MbarHistories
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.TensorSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety

open PTX PTX.AsyncCopy PTX.MBarrier

/-- Any fault in an actual mbarrier history comes from an arrival or a transaction update. -/
theorem mbarFaultIsUpdate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {object : Loc} {r : Record Ref} (hRecord : r ∈ X.objects object)
    (hFault : r.fault.isSome) :
    (∃ count tx, r.action = .arrive count tx) ∨ ∃ bytes, r.action = .completeTx bytes := by
  have noInitOrPoll
      (h : (∃ count, r.action = .init count) ∨
        ∃ parity waited, r.action = .pollParity parity waited) : False := by
    rw [actualInitOrPollClean hp hX hRecord h] at hFault
    cases hFault
  cases hAction : r.action with
  | init count => exact (noInitOrPoll (.inl ⟨count, hAction⟩)).elim
  | pollParity parity waited => exact (noInitOrPoll (.inr ⟨parity, waited, hAction⟩)).elim
  | arrive count tx => exact .inl ⟨count, tx, rfl⟩
  | completeTx bytes => exact .inr ⟨bytes, rfl⟩
  | inval =>
    exact (objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) object r hRecord hAction).elim
  | increment =>
    cases record_source hX.tma.2.2.1 hRecord with
    | increment _ he _ => exact (Loader.noIncrementingCopyArrival hX ⟨_, he⟩).elim
    | init _ _ ha | inval _ _ ha | wait _ _ ha | arrive _ _ ha | tensor _ _ _ ha
    | arriveOn _ _ _ _ ha | bulk _ _ _ _ ha | commit _ _ _ ha | clc _ _ _ _ ha =>
      rw [hAction] at ha
      cases ha

/-- An mbarrier rejection must come from an actual counter update or transaction fault. -/
theorem tmaUnsafeCases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hUnsafe : TmaUnsafe l m X) :
    ∃ (object : Loc) (r : Record Ref), r ∈ X.objects object ∧ r.fault.isSome ∧
      ((∃ count tx, r.action = .arrive count tx) ∨ ∃ bytes, r.action = .completeTx bytes) := by
  rcases hUnsafe with ⟨object, r, hRecord, hFault⟩ | ⟨object, r, hRecord, hBad⟩ |
    ⟨ref, a, mode, i, object, count, loc, hAccess, hInit, hCover, hOverlap, _, _⟩ |
    hOverlap | hMasked
  · exact ⟨object, r, hRecord, hFault, mbarFaultIsUpdate hp hX hRecord hFault⟩
  · exact (hBad (actualObjectPublished hp hX hRecord)).elim
  · have hUse := Execution.UsesMbar.of_init hInit
    cases mode
    · exact (mbarReadDisjoint hp hX hUse hAccess hCover hOverlap).elim
    · exact (writeIntentOutsideMbar hp hX hUse hAccess hCover hOverlap).elim
  · exact (Loader.noCpAsyncOverlap hp hX hOverlap).elim
  · exact (noMaskedRangeUnalloc hX hMasked).elim

/-- The actual mbarrier histories are safe with the launch offsets preserved. -/
theorem noTmaUnsafe {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) :
    ¬ TmaUnsafe l m X := by
  intro hUnsafe
  obtain ⟨object, r, hRecord, hFault, hUpdate⟩ := tmaUnsafeCases hp hX hUnsafe
  rw [Protocol.mbarUpdatesClean hp hX hCuQ hRecord hUpdate] at hFault
  cases hFault

end PTX.Kernels.TmlFa4Fwd.Safety
