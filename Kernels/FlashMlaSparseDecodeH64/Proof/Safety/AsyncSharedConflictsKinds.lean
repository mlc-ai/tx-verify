-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorLoadSources
import Lemmas.Tensor.TensorCopy

public section

/-! # Pending asynchronous accesses to shared memory -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Each asynchronous shared access is a tensor load destination, a tensor store source,
or a Tensor Core operand. -/
inductive SharedAsyncKind : Part → Bool → Prop
  | load (x y b : Nat) : SharedAsyncKind (.write (.load x y b)) true
  | output (x y b : Nat) : SharedAsyncKind (.read (.store x y b)) false
  | operand (isB : Bool) (index : Nat) : SharedAsyncKind (.mmaRead isB index) false

private theorem tensor_store_destination_global {s : TensorStore.Spec} {x y b : Nat} {l : Loc}
    (h : TensorStore.writeLoc s x y b = some l) : l.space = .global := by
  unfold TensorStore.writeLoc at h
  obtain ⟨_, _, hDst⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, hLoc⟩ := Option.map_eq_some_iff.mp hDst
  rw [← hLoc]

/-- Classification by actual issue operands, which applies before the stage is performed. -/
theorem shared_async_kind (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {p : Part} {a : Acc} {w : Bool} {l : Loc}
    (h : X.Intent (.async i p) a w) (hCover : a.Covers l) (hShared : l.space = .shared) :
    SharedAsyncKind p w := by
  have hSpace : a.loc.space = .shared := hCover.1.symm.trans hShared
  obtain ⟨rfl, hf⟩ := h
  cases p <;> try contradiction
  case readLoad =>
    obtain ⟨_, _, _, hLoc, _⟩ := hf
    exact Space.noConfusion ((TensorTransfer.sourceLoc_global hLoc).symm.trans hSpace)
  case readStore => exact .output _ _ _
  case readPrefetch =>
    obtain ⟨_, _, hi, _, _⟩ := hf
    exact (TensorLoadSources.no_tensor_prefetch hX hi).elim
  case readCopy =>
    rcases hf with ⟨_, hi, _⟩ | hi
    · exact (GlobalWrites.no_copy hX hi).elim
    · exact (GlobalWrites.no_bulk_prefetch hX hi).elim
  case writeLoad => exact .load _ _ _
  case writeStore =>
    obtain ⟨_, _, _, hLoc, _⟩ := hf
    exact Space.noConfusion ((tensor_store_destination_global hLoc).symm.trans hSpace)
  case oldStore =>
    obtain ⟨_, _, _, _, hLoc, _⟩ := hf
    exact Space.noConfusion ((tensor_store_destination_global hLoc).symm.trans hSpace)
  case writeCopy =>
    obtain ⟨_, hi, _⟩ := hf
    exact (GlobalWrites.no_copy hX hi).elim
  case writeElem =>
    obtain ⟨_, hi, _⟩ := hf
    exact (GlobalWrites.no_copy hX hi).elim
  case oldElem =>
    obtain ⟨_, _, hi, _⟩ := hf
    exact (GlobalWrites.no_copy hX hi).elim
  case writeCta =>
    obtain ⟨_, _, hi, _, _⟩ := hf
    exact (GlobalWrites.no_clc hX hi).elim
  case mmaRead => exact .operand _ _

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts
