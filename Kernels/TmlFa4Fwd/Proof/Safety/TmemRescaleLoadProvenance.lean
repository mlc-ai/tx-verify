-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleLoadSources
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemReadConflicts
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Tcgen05.TmemLatestSource
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread Thread.Correction Thread.Scores Protocol.Scores
open PTX.Kernels.TmlFa4Fwd.Mma (pvSite)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

theorem rescaleLoadMmaOrder {load other : EvId} {cell : Cell} {stage : Fin 2}
    (hLoad : RescaleLoadCell l X load cell stage) (seen : RescaleStatisticsScore l X load stage)
    (hMma : X.MmaCell other cell) :
    DoneBefore l X other load ∨ WaitBefore l X .waitLd load other := by
  obtain ⟨col,hCell⟩ := hLoad.geometry hp hX
  have hOwner : cell.cta = load.1/l.block := congrArg Cell.cta hCell
  have hRange : outputColumn stage ≤ cell.column ∧ cell.column < outputColumn stage+128 := by
    rw [hCell]
    have := col.isLt
    exact ⟨by dsimp; omega,by dsimp; omega⟩
  have hCta := (mmaWrittenCellCta hp hX hMma).symm.trans hOwner
  obtain ⟨_,_,_,_,_,_,hIssue,hWrite⟩ := hMma
  obtain ⟨block,step,d,op,acc,mask,_,_,hStage,hPv,_⟩ :=
    mmaAccumulatorOnTile hp hX (tile := .rescale stage) hRange hIssue
      (writeCell_resultCell hWrite)
  have hScope := Thread.Correction.OutputRescaleLoad.sameCtaMma hX hLoad.loadEvent hIssue hCta
  by_cases hPast : other.2 < seen.commit.2
  · exact .inl (seen.doneBeforeEarlierMma hp hX hIssue hScope hPast)
  · obtain ⟨wait,hWait⟩ := hPv.probabilityAcquire hp hX 0 (.inl rfl)
    have hAcquire : MmaProbabilityAcquire l X other stage 0 wait := hStage ▸ hWait
    exact .inr (rescaleLoadBeforeGuardedMma hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
      stage hLoad.loadEvent hIssue hScope seen (Nat.le_of_not_lt hPast) hAcquire)

omit hp hX hCuQ in
theorem rescaleWriterTile {cell : Cell} {stage : Fin 2} {tile : TensorStoreTile}
    {l : Launch} {writer : EvId} (hFoot : TensorStoreFootprint l writer cell tile)
    (hRange : outputColumn stage ≤ cell.column ∧ cell.column < outputColumn stage + 128) :
    tile = .rescale stage := by
  have hLo := hRange.1
  have hHi := hRange.2
  have hStoreLo := hFoot.columnLo
  have hStoreHi := hFoot.columnHi
  cases tile with
  | probability k =>
    have hScore := scoreColumn_range k
    have hProb := probabilityColumn_range k
    simp only [TensorStoreTile.columns] at hStoreHi
    unfold outputColumn at hLo
    omega
  | rescale k =>
    simp only [TensorStoreTile.columns,outputColumn] at hLo hHi hStoreLo hStoreHi
    have hSame : k = stage := Fin.ext (by omega)
    rw [hSame]

/-- The rescale load has a stable Tensor Memory source in every consistent prefix. -/
theorem rescaleLoadReadSource {load : EvId} {cell : Cell} {stage : Fin 2}
    (hLoad : RescaleLoadCell l X load cell stage) :
    ∃ source, ReadSource l X .ld source load cell := by
  have hWrites := tensorWritesSafeOfCuQ hp hX hCuQ
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  obtain ⟨col,hCell⟩ := hLoad.geometry hp hX
  have hOwner : cell.cta = load.1/l.block := congrArg Cell.cta hCell
  have hRange : outputColumn stage ≤ cell.column ∧ cell.column < outputColumn stage+128 := by
    rw [hCell]
    have := col.isLt
    exact ⟨by dsimp; omega,by dsimp; omega⟩
  obtain ⟨seen,source,_,_,_,_,_,hSource,_,hDone⟩ := rescaleLoadPvCandidate hLoad hp hX hCuQ
  apply readSourceOfCandidate hX hGuard hWrites (candidate := source) _ _
    (.inl hSource) (.inl (.inl hDone))
  · intro other hOther
    rcases hOther with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
    · rcases rescaleLoadMmaOrder hp hX hCuQ hLoad seen hMma with h | h
      · exact .inl (.inl (.inl h))
      · exact .inr (.inl h)
    · obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
      have hTile := rescaleWriterTile hFoot hRange
      exact rescaleLoadStoreOrdered hp hX hLoad hStore (hTile ▸ hFoot)
    · exact (noTensorCopyOperandIssue hX hCopy).elim
    · exact (noTensorShiftIssue hX hShift).elim
  · intro _ _ _ c r hr hCover release hRelease
    obtain ⟨hReleaseOwner,hDealloc⟩ := allocationReleaseInOwnerCta hX hr hRelease
    obtain ⟨_,_,_,hCellCta,_,_,_⟩ := hCover
    exact .inl (tensorOperationsCompletedBeforeRelease hp hX hCuQ
      (hOwner.symm.trans (hCellCta.trans hReleaseOwner.symm)) hDealloc)

/-- A rescale load receives the value of its stable writer. Actual MMA sources
are completed and an ordinary correction store already carries its word. -/
theorem rescaleLoadSourceValue (hValues : ∀ i, CompletedValues l Assumptions.all X i) {load : EvId}
    {cell : Cell} {stage : Fin 2} (hLoad : RescaleLoadCell l X load cell stage) :
    ∃ source value, ReadSource l X .ld source load cell ∧
      Wrote l Assumptions.all X source cell value := by
  obtain ⟨source,hSource⟩ := rescaleLoadReadSource hp hX hCuQ hLoad
  rcases hSource.2.1 with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
  · obtain ⟨seen,_⟩ := rescaleLoadStatisticsObservedScore hp hX hCuQ hLoad.loadEvent
    rcases rescaleLoadMmaOrder hp hX hCuQ hLoad seen hMma with h | h
    · obtain ⟨v,hV⟩ := hValues source (h.done hX.tcCommit) cell hMma
      exact ⟨source,v,hSource,.inl hV⟩
    · have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
      exact (tcStep_acyclic hX hGuard source (hSource.2.2.1.tcStep.trans h.tcStep)).elim
  · obtain ⟨a,vs,shape,j,hStore,hJ,hCell⟩ := hStore
    exact ⟨source,vs[j],hSource,.inr (.inl
      ⟨a,vs,shape,j,hStore,List.getElem?_eq_some_iff.mpr ⟨hJ,rfl⟩,hCell⟩)⟩
  · exact (noTensorCopyOperandIssue hX hCopy).elim
  · exact (noTensorShiftIssue hX hShift).elim


/-- An actual rescale load sees FP32 values if the ordered earlier MMA and rescale
writers have been evaluated. All cases come from the same output-stage cells. -/
theorem rescaleLoadWordOfEarlierValues {load : EvId} {cell : Cell} {stage : Fin 2}
    (hLoad : RescaleLoadCell l X load cell stage) {address j : Nat} {vals : List Value}
    {shape : TcShape} (ht : X.TLd load address vals shape) (hc : LoadCell l X load j cell)
    (hMmaValue : ∀ source, Relation.TransGen (TcStep l X) source load →
      X.async.mmaDone source = true → X.MmaCell source cell →
      ∃ x, Result l Assumptions.all X source cell (.float .f32 x))
    (hStoreValue : ∀ source, Relation.TransGen (TcStep l X) source load →
      ∀ v, TensorStoreFootprint l source cell (.rescale stage) → StoreValue l X source cell v →
      ∃ x, v = .float .f32 x) :
    ∃ x, vals[j]? = some (.float .f32 x) := by
  obtain ⟨source,hSource⟩ := rescaleLoadReadSource hp hX hCuQ hLoad
  have hBefore := hSource.2.2.1.tcStep
  have hValue : ∃ x, Wrote l Assumptions.all X source cell (.float .f32 x) := by
    rcases hSource.2.1 with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
    · obtain ⟨seen,_⟩ := rescaleLoadStatisticsObservedScore hp hX hCuQ hLoad.loadEvent
      rcases rescaleLoadMmaOrder hp hX hCuQ hLoad seen hMma with h | h
      · obtain ⟨x,hx⟩ := hMmaValue source hBefore (h.done hX.tcCommit) hMma
        exact ⟨x,.inl hx⟩
      · have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
        exact (tcStep_acyclic hX hGuard source (hBefore.trans h.tcStep)).elim
    · obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
      obtain ⟨col,hCell⟩ := hLoad.geometry hp hX
      have hRange : outputColumn stage ≤ cell.column ∧ cell.column < outputColumn stage+128 := by
        rw [hCell]
        have := col.isLt
        exact ⟨by dsimp; omega,by dsimp; omega⟩
      have hTile := rescaleWriterTile hFoot hRange
      obtain ⟨a,vs,sh,n,hSt,hn,hCell⟩ := hStore
      have hv : StoreValue l X source cell vs[n] :=
        ⟨a,vs,sh,n,hSt,List.getElem?_eq_some_iff.mpr ⟨hn,rfl⟩,hCell⟩
      obtain ⟨x,hx⟩ := hStoreValue source hBefore _ (hTile ▸ hFoot) hv
      exact ⟨x,.inr (.inl (hx ▸ hv))⟩
    · exact (noTensorCopyOperandIssue hX hCopy).elim
    · exact (noTensorShiftIssue hX hShift).elim
  obtain ⟨x,hx⟩ := hValue
  exact ⟨x,hX.tcRead.1.f32 ht hc hSource hx⟩

end PTX.Kernels.TmlFa4Fwd.Safety
