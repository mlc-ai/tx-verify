-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.TcCommit

@[expose] public section

/-!
# Asynchronous writes land in shared memory

The kernel's asynchronous write stages are the tensor loads'. A tensor store, a cancellation
response and a linear copy do not occur, and a tensor prefetch has no write stage. A tensor load
writes the shared tile of its box, in the memory space of the box's shared base
(`TensorBox.sharedLoc`), which every copy of the kernel puts in shared memory
(`Tensor.issue_fill`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every write stage of an asynchronous operation writes shared memory.** -/
theorem asyncWritesShared (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hm : KvMapOnly Q X) : AsyncWritesShared X := by
  intro i p a h
  obtain ⟨hw, hfp⟩ := h
  have hwr : ∃ sl, p = .write sl := by
    cases p <;> simp only [AsyncCopy.Part.writes] at hw <;> first | exact ⟨_, rfl⟩ | cases hw
  obtain ⟨sl, rfl⟩ := hwr
  cases sl with
  | store x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorStore hX)
  | load x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, hloc, -⟩ := hfp
    obtain ⟨-, -, hsh⟩ := issue_fill hpre hX hf hm he
    simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hloc
    obtain ⟨slot, -, hl⟩ := hloc
    rw [← hl]
    exact hsh
  | cta c =>
    obtain ⟨s, targets, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_clc hX)
  | copy =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_copy hX)
  | prefetch x y k => exact hfp.elim
  | elem j =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_copy hX)

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
