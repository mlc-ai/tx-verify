-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Input
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The input copies are safe tensor copies

Every tensor copy zero-fills `bf16` elements (`input_noTensorUnsafe`) and its map has the backing
the launch supplies (`input_backing`): what `Top/Safety` reads of `Proof/TensorSafety`, on the new
machine. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every tensor copy writes a scalar byte**, from a backed operand or from the zero fill. -/
theorem input_noTensorUnsafe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : ¬ TensorUnsafe X := by
  rintro ⟨i, o, slot, content, ho, hw, hBad⟩
  obtain ⟨⟨address, pc, hi⟩, hok, _⟩ := hX.tensor i o ho
  obtain ⟨-, j, org, mb, -, hs⟩ := input_box hp hX hFw hi
  obtain ⟨-, -, hFormat', -, hFill'⟩ := input_map p j
  have hFill : o.spec.descriptor.fill = .zero := by rw [hs]; exact hFill'
  have hFormat : o.spec.descriptor.format = .bf16 := by rw [hs]; exact hFormat'
  have he := hok.writes slot content hw
  unfold TensorCopy.source at he
  cases hLoc : o.spec.globalAddress slot with
  | none =>
    simp only [hLoc, hFill, hFormat] at he
    subst content
    simp [TensorCopy.Content.byte, TensorCopy.zeroValue] at hBad
  | some a =>
    rw [hLoc] at he
    obtain ⟨b, _, rfl⟩ := he
    cases hBad

/-- **A tensor copy's map has its backing.** -/
theorem input_backing (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {addr : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i addr s) :
    ¬ TensorBackingMissing L m s.descriptor s.origin s.rows := by
  intro hBad
  obtain ⟨pc, he⟩ := hi
  obtain ⟨-, j, org, mb, -, rfl⟩ := input_box hp hX hFw he
  obtain ⟨-, -, -, -, -, hBias⟩ := hp.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩ (by simp)
  obtain ⟨-, -, -, -, -, hQ⟩ := hp.maps 9 p.qMapAddress ⟨2, p.qMap⟩ (by simp)
  have hl := hBad.1
  apply hBad.2.2
  change (Loader.inputMap p (Loader.inputSite j)).allocationClass = _ at hl
  change TensorLargeBacking L m (Loader.inputMap p (Loader.inputSite j)).base
  generalize hM : Loader.inputMap p (Loader.inputSite j) = M at hl ⊢
  unfold Loader.inputMap at hM
  split at hM <;> subst hM
  · exact hBias hl
  · exact hQ hl

end PTX.Kernels.TmlFa4Fwd.Proof
