-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.TmemCellBounds
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Thread

private theorem ordinaryTensorAccessLifetime {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {i : EvId} {cell : TcMma.Cell}
    (hCell : TensorDataEvent X i ∧ cell.cta = i.1/l.block ∧ cell.column < 512) :
    (∃ cta r, r ∈ X.tmemHistory cta ∧ Tmem.Pair.Covers l X r cell.cta i cell.column) ∧
      ∀ cta r, r ∈ X.tmemHistory cta → Tmem.Pair.Covers l X r cell.cta i cell.column →
        ∀ d, Tmem.Pair.ReleaseOf l X r d → TcMma.CompletedBefore l X i d := by
  obtain ⟨hEvent,hOwner,hColumn⟩ := hCell
  obtain ⟨r,hr,hCover⟩ := allocatedTensorColumn hp hX hEvent hColumn
  refine ⟨⟨_,r,hr,hOwner.symm ▸ hCover⟩,?_⟩
  intro cta rec hRec hCovers d hRelease
  obtain ⟨hScope,hDealloc⟩ := allocationReleaseInOwnerCta hX hRec hRelease
  obtain ⟨_,_,_,hRecOwner,_,_,_⟩ := hCovers
  exact tensorOperationsCompletedBeforeRelease hp hX hCuQ
    (hOwner.symm.trans (hRecOwner.trans hScope.symm)) hDealloc

/-- Every Tensor Memory access is covered by an allocation and completes before release. -/
theorem tensorAccessSafe {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) : Tmem.Pair.AccessSafe l X := by
  intro i cell hAccess
  have finish
      (h : (∃ cta r, r ∈ X.tmemHistory cta ∧ Tmem.Pair.Covers l X r cell.cta i cell.column) ∧
        ∀ cta r, r ∈ X.tmemHistory cta → Tmem.Pair.Covers l X r cell.cta i cell.column →
          ∀ d, Tmem.Pair.ReleaseOf l X r d → TcMma.CompletedBefore l X i d) :
      (∃ cta r, r ∈ X.tmemHistory cta ∧ Tmem.Pair.Covers l X r cell.cta i cell.column) ∧
        ∀ cta r, r ∈ X.tmemHistory cta → Tmem.Pair.Covers l X r cell.cta i cell.column →
          ∀ d, Tmem.Pair.ReleaseOf l X r d →
            TcMma.CompletedBefore l X i d ∨ Tmem.Pair.FreshAfter l X d i cell.cta cell.column :=
    ⟨h.1, fun cta r hr hCover d hd => .inl (h.2 cta r hr hCover d hd)⟩
  rcases hAccess with hMma | ⟨_,hLoad⟩ | hStore | hCopy | hShift | hShiftRead
  · exact finish (mmaAccessLifetime hp hX hCuQ hMma)
  · exact finish (ordinaryTensorAccessLifetime hp hX hCuQ (tensorLoadCellRange hp hX hLoad))
  · exact finish (ordinaryTensorAccessLifetime hp hX hCuQ (tensorStoreCellRange hp hX hStore))
  · obtain ⟨_,_,_,_,hIssue,_⟩ := hCopy
    exact (noTensorCopyOperandIssue hX hIssue).elim
  · obtain ⟨_,hIssue,_⟩ := hShift
    exact (noTensorShiftIssue hX hIssue).elim
  · obtain ⟨_,hIssue,_⟩ := hShiftRead
    exact (noTensorShiftIssue hX hIssue).elim

end PTX.Kernels.TmlFa4Fwd.Safety
