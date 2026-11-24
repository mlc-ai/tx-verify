-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxReads
public import Lemmas.Flow.ReadRunTyMore

@[expose] public section

/-! # Shapes of the softmax words

When the words of a state are single-precision numbers, their packs are pairs of them
(`has_join`) and their selected halves are numbers (`half_has`): the shapes the read runs of the
softmax need (`ReadRunTy`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem has_join {a b : Value} (ha : RTy.Has .f32 a) (hb : RTy.Has .f32 b) :
    RTy.Has .f32x2 (joinValue a b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x, y, rfl⟩

theorem half_has {w : Nat → Value} (hf : ∀ k < 128, RTy.Has .f32 (w k)) {k : Nat}
    (hk : k < 128) : RTy.Has .f32 (half w k) := by
  unfold half
  split
  · obtain ⟨x, hx⟩ := hf k hk
    obtain ⟨y, hy⟩ := hf (k + 1) (by omega)
    exact ⟨x, by rw [hx, hy]; rfl⟩
  · obtain ⟨x, hx⟩ := hf (k - 1) (by omega)
    obtain ⟨y, hy⟩ := hf k hk
    exact ⟨y, by rw [hx, hy]; rfl⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
