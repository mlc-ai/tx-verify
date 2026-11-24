-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.SharedOwnership
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Lemmas.Order.Order

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Every asynchronous memory footprint is in global or shared memory. -/
theorem asyncMemorySpace {i : EvId} {part : AsyncCopy.Part} {a : Acc}
    (h : X.AsyncFootprint i part a) :
    a.loc.space = .global ∨ a.loc.space = .shared := by
  cases part <;> try exact False.elim h
  case mmaRead isB index =>
    exact .inr (mmaSharedFootprintIssue hX h.2).1
  case readCopy =>
    rcases h with ⟨s, hi, rfl⟩ | hPrefetch
    · exact .inl (actualCopyShape hX hi).srcGlobal
    · exact (noBulkPrefetch hX hPrefetch).elim
  case writeCopy =>
    obtain ⟨s, hi, _, rfl⟩ := h
    exact .inr (actualCopyShape hX hi).dstShared
  case readStore x y k =>
    obtain ⟨s, _, hi, hRead, _⟩ := h
    obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hRead
    obtain ⟨_, _, _, hAt⟩ := actualTensorOutputSharedRange hp hX hi slot
    exact .inr (congrArg Loc.space (hLoc.symm.trans hAt))
  case writeStore x y k =>
    obtain ⟨_, _, _, hLoc, _⟩ := h
    exact .inl (Execution.store_writeLoc_global hLoc)
  case oldStore x y k =>
    obtain ⟨_, _, _, _, hLoc, _⟩ := h
    exact .inl (Execution.store_writeLoc_global hLoc)
  case readLoad x y k =>
    obtain ⟨_, _, _, hLoc, _⟩ := h
    exact .inl (Execution.tensor_readLoc_global hLoc)
  case writeLoad x y k =>
    obtain ⟨s, _, hi, hWrite, _⟩ := h
    obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hWrite
    obtain ⟨_, _, _, hAt⟩ := actualTensorInputSharedRange hp hX hi slot
    exact .inr (congrArg Loc.space (hLoc.symm.trans hAt))
  case readPrefetch x y k =>
    obtain ⟨_, _, _, hLoc, _⟩ := h
    exact .inl (TensorTransfer.sourceLoc_global hLoc)
  case writeElem j =>
    obtain ⟨s, hi, hAt⟩ := h
    simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (actualCopyShape hX hi).whole] at hAt
  case oldElem j =>
    obtain ⟨s, _, hi, hw, _⟩ := h
    rw [(actualCopyShape hX hi).whole] at hw
    cases hw
  case writeCta owner =>
    obtain ⟨_, _, hi, _, _⟩ := h
    exact (noClcIssue hX hi).elim

private theorem localIntentOwner {e : AsyncCopy.Ref} {a : Acc} {w : Bool} {loc : Loc}
    (hIntent : X.Intent e a w) (hLocal : loc.space = .local) (hCover : a.Covers loc) :
    ∃ j, e = .thread (loc.cta, j) ∧ X.Access (loc.cta, j) a w := by
  have hSpace := hCover.1.symm.trans hLocal
  cases e with
  | async i part =>
    rcases asyncMemorySpace hp hX hIntent.2 with h | h <;> rw [h] at hSpace <;> cases hSpace
  | thread i =>
    rcases hIntent with ⟨_, hRead, rfl⟩ | ⟨_, hWrite, rfl⟩ | ⟨_, _, hRmw⟩
    · have hOwner := hCover.2.1.trans (Loader.localReadOwned hX hRead hSpace)
      obtain ⟨g, j⟩ := i
      change loc.cta = g at hOwner
      obtain rfl := hOwner
      exact ⟨j, rfl, hRead.access⟩
    · exact localWriteOwner hX (w := .thread i) (.inl hWrite) hLocal hCover
    · exact (noActualRmw hX hRmw).elim

/-- Conflicting local-memory intents have the same owner and are ordered by program order. -/
theorem localConflictOrdered {e f : AsyncCopy.Ref} {a b : Acc} {loc : Loc} (h : Conflict X e f a b)
    (hLocal : loc.space = .local) (ha : a.Covers loc) (hb : b.Covers loc) :
    ByteCausality l X loc e f ∨ ByteCausality l X loc f e := by
  obtain ⟨hne, wa, wb, hA, hB, _, _⟩ := h
  obtain ⟨i, rfl, hi⟩ := localIntentOwner hp hX hA hLocal ha
  obtain ⟨j, rfl, hj⟩ := localIntentOwner hp hX hB hLocal hb
  have hIndex : i ≠ j := fun he => hne (congrArg (fun n => AsyncCopy.Ref.thread (loc.cta, n)) he)
  rcases Nat.lt_or_gt_of_ne hIndex with hLt | hGt
  · exact .inl (.direct (.inl (.single (.inl (po_of_overlap hi hj rfl hLt ⟨loc, ha, hb⟩)))))
  · exact .inr (.direct (.inl (.single (.inl (po_of_overlap hj hi rfl hGt ⟨loc, hb, ha⟩)))))

private theorem noConstantIntentWrite {ref : AsyncCopy.Ref} {a : Acc}
    (hSpace : a.loc.space = .const) :
    ¬ X.Intent ref a true := by
  intro hIntent
  cases ref with
  | async i part =>
    rcases asyncMemorySpace hp hX hIntent.2 with h | h <;> rw [h] at hSpace <;> cases hSpace
  | thread i =>
    rcases hIntent with ⟨_, _, hBad⟩ | ⟨_, hWrite, _⟩ | ⟨_, _, hRmw⟩
    · cases hBad
    · exact noConstantWrite hX hWrite hSpace
    · exact noActualRmw hX hRmw

/-- An unordered conflicting byte belongs to global or shared memory. -/
theorem unorderedConflictSpace {e f : AsyncCopy.Ref} {a b : Acc} {loc : Loc}
    (h : Conflict X e f a b) (ha : a.Covers loc) (hb : b.Covers loc)
    (hef : ¬ ByteCausality l X loc e f) (hfe : ¬ ByteCausality l X loc f e) :
    loc.space = .global ∨ loc.space = .shared := by
  cases hSpace : loc.space with
  | global => exact .inl rfl
  | shared => exact .inr rfl
  | «local» => exact ((localConflictOrdered hp hX h hSpace ha hb).elim hef hfe).elim
  | const =>
    obtain ⟨_, wa, wb, hwA, hwB, rfl | rfl, _⟩ := h
    · exact (noConstantIntentWrite hp hX (ha.1.symm.trans hSpace) hwA).elim
    · exact (noConstantIntentWrite hp hX (hb.1.symm.trans hSpace) hwB).elim

private theorem sharedIntentOwner {ref : AsyncCopy.Ref} {a : Acc} {w : Bool} {loc : Loc}
    (h : X.Intent ref a w) (hCover : a.Covers loc) (hShared : loc.space = .shared) :
    loc.cta = ref.issuer.1 / l.block := by
  have hSpace := hCover.1.symm.trans hShared
  refine hCover.2.1.trans ?_
  cases ref with
  | async i part => exact asyncFootprintOwnsShared hp hX h.2 hSpace
  | thread i =>
    rcases h with ⟨_, hRead, _⟩ | ⟨_, hWrite, _⟩ | ⟨_, _, hRmw⟩
    · exact Loader.sharedReadOwned hX hRead hSpace
    · exact sharedWriteOwned hX hWrite hSpace
    · exact (noActualRmw hX hRmw).elim

private theorem unorderedConflictScope {e f : AsyncCopy.Ref} {a b : Acc} {loc : Loc}
    (h : Conflict X e f a b) (ha : a.Covers loc) (hb : b.Covers loc)
    (hef : ¬ ByteCausality l X loc e f) (hfe : ¬ ByteCausality l X loc f e) :
    loc.space = .global ∨ (loc.space = .shared ∧ e.issuer.1 / l.block = f.issuer.1 / l.block) := by
  rcases unorderedConflictSpace hp hX h ha hb hef hfe with hGlobal | hShared
  · exact .inl hGlobal
  · obtain ⟨_, _, _, hA, hB, _, _⟩ := h
    exact .inr ⟨hShared,
      (sharedIntentOwner hp hX hA ha hShared).symm.trans (sharedIntentOwner hp hX hB hb hShared)⟩

omit hp hX in
/-- A conflicting shared or global access pair that violates a byte-order safety check. -/
def MemoryConflict (l : Launch) (X : Execution) : Prop :=
  ∃ e f a b loc,
    (loc.space = .global ∨ (loc.space = .shared ∧ e.issuer.1 / l.block = f.issuer.1 / l.block)) ∧
    Conflict X e f a b ∧
    a.Covers loc ∧ b.Covers loc ∧ ¬ ByteCausality l X loc e f ∧ ¬ ByteCausality l X loc f e ∧
    (¬ a.SameFootprint b ∨ ¬ MorallyStrong l X e f a b ∧ ¬ SameValueWrites X e f a b)

/-- Data races and mixed-size conflicts can be checked on shared and global bytes alone. -/
theorem memoryConflictCases (hBad : Race l X ∨ Mixed l X) : MemoryConflict l X := by
  rcases hBad with ⟨e, f, a, b, loc, h, hFoot, ha, hStrong, hef, hfe, hValue⟩ |
    ⟨e, f, a, b, loc, h, hFoot, ha, hb, hef, hfe⟩
  · have hb := (hFoot.covers loc).mp ha
    exact ⟨e, f, a, b, loc, unorderedConflictScope hp hX h ha hb hef hfe, h, ha, hb, hef, hfe,
      .inr ⟨hStrong, hValue⟩⟩
  · exact ⟨e, f, a, b, loc, unorderedConflictScope hp hX h ha hb hef hfe, h, ha, hb, hef, hfe,
      .inl hFoot⟩

end PTX.Kernels.TmlFa4Fwd.Safety
