-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

/-! The shared tensor-map checks (THREAD-TENSOR-MAP-ADDRESS `tensorMap`). -/
namespace PTX
noncomputable section

/-- A tensor map that passes `tensorMap` is the published, valid map at the resolved address. -/
theorem tensorMap_ok {L : Launch} {g : Nat} {t : TState} {map : Opnd} {cs : List Opnd}
    {mode : TensorMode} {a outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (h : tensorMap L g t map cs mode = .ok (a, ⟨outer, d⟩)) :
    tensorMapAddress L g t map = .ok a ∧ L.tensorMaps a = some ⟨outer, d⟩ ∧
      TensorDescriptor.Valid d ∧ cs.length = mode.coordinates outer := by
  unfold tensorMap at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (split at h <;> (try (cases h; done)))
  all_goals (cases h; exact ⟨by assumption, by assumption, by assumption, by assumption⟩)

end
end PTX
