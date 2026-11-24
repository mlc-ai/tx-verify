-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # `TensorStoreUnsafe`

Every tensor store is a store lane's copy of a staged stage (`OutputFacts.store_tma`), not a
reduction (`StoreSrc`), so no performed element lacks a reduction rule (`no_reduce`), and the
kernel has no linear copy, so no linear reduction either. Its box starts at an aligned coordinate
(`StoreBoxes`: the O map's 64-element inner box at column `64 h` and row `512 m + 256 st + 128 r`);
the store's thread rule checks that alignment, so `TensorStoreUnsafe` does not use it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every tensor store's box starts at an aligned coordinate. -/
def StoreBoxes (X : Execution) : Prop :=
  ∀ i addr s, X.TensorStoreIssue i addr s → TensorDescriptor.BoxAligned s.descriptor s.origin

/-- The kernel's tensor stores are not reductions. -/
theorem no_reduce (hX : Consistent L kernel asms mem0 X) (ht : OutputFacts L X) :
    ∀ i addr s, X.TensorStoreIssue i addr s → s.reduce = none := by
  rintro ⟨g, k⟩ addr s ⟨pc, he⟩
  obtain ⟨-, st, -, hsrc⟩ := ht.store_tma (event_thread_lt hX he) he
  exact hsrc.1

/-- **No tensor store is unsafe**: the kernel's tensor stores are not reductions, and it has no
linear copy. -/
theorem no_tensorStoreUnsafe (hX : Consistent L kernel asms mem0 X) (ht : OutputFacts L X)
    (htm : TmemFacts L X) : ¬ TensorStoreUnsafe asms X := by
  rintro (⟨i, o, red, x, y, hio, hred, -⟩ | h)
  · obtain ⟨⟨addr, hi⟩, -⟩ := hX.store i o hio
    rw [no_reduce hX ht i addr o.spec hi] at hred
    cases hred
  · exact TensorStore.not_copyReduceNoRule_of_none (fun _ _ ⟨_, he⟩ => (htm.no_bulk he).elim) h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
