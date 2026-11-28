-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async

@[expose] public section

/-! # ERR-TENSOR-FILL-VALUE: tensor loads fill with a defined value

The safety class of Core's `Unsafe` this file owns (`TensorUnsafe`), proved by `Safe.noTensor`:
every tensor load reads through the query map or a cache map (`tensor_load_map`), each with the
zero fill of a format that has a zero (bf16, u32), so every written byte is a copied byte or a
byte of the zero. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The fill and format of the kernel's load maps. -/
private theorem load_fill (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {i : EvId} {a : Nat}
    {s : TensorCopy.Spec} (h : X.TensorIssue i a s) :
    s.descriptor.fill = .zero ∧ (TensorCopy.zeroValue s.descriptor.format).isSome := by
  have hQ : ∀ y : Σ n, TensorDescriptor.Descriptor n,
      y = ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩ →
      y.2.fill = .zero ∧ (TensorCopy.zeroValue y.2.format).isSome := by
    rintro y rfl
    exact ⟨rfl, rfl⟩
  have hK : ∀ y : Σ n, TensorDescriptor.Descriptor n, KvMap P y →
      (TensorMode.fourRows.transfer y.2).fill = .zero ∧
        (TensorCopy.zeroValue (TensorMode.fourRows.transfer y.2).format).isSome := by
    rintro y (rfl | ⟨-, rfl⟩) <;> exact ⟨rfl, rfl⟩
  rcases tensor_load_map hp hX hFw h with hq | ⟨d0, hd, hk⟩
  · exact hQ _ hq
  · rw [hd]
    exact hK _ hk

/-- **ERR-TENSOR-FILL-VALUE**: tensor loads fill with a defined value. -/
theorem Safe.noTensor (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ TensorUnsafe X := by
  rintro ⟨i, o, slot, content, ho, hw, hBad⟩
  obtain ⟨⟨address, pc, hi⟩, hok, _⟩ := hX.tensor i o ho
  obtain ⟨hFill, hFormat⟩ := load_fill hp hX hFw ⟨pc, hi⟩
  have he := hok.writes slot content hw
  unfold TensorCopy.source at he
  cases hLoc : o.spec.globalAddress slot with
  | none =>
    simp only [hLoc, hFill] at he
    subst content
    simp only [TensorCopy.Content.byte, Option.map_eq_none_iff] at hBad
    rw [hBad] at hFormat
    cases hFormat
  | some a =>
    rw [hLoc] at he
    obtain ⟨b, _, rfl⟩ := he
    cases hBad

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
