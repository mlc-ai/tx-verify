-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorThread
public import Lemmas.Tensor.TensorMap

@[expose] public section

/-! The tensor-store issue rule (THREAD-TENSOR-STORE): what a successful store template records. -/
namespace PTX
noncomputable section

/-- A tensor-store template is a fault or one store issue continuing at the next instruction,
whose specification is `tensorStoreSpec`'s. -/
theorem tensorStoreTmpl_issue {L : Launch} {g : Nat} {t u : TState} {map : Opnd} {cs : List Opnd}
    {src : Nat} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {a : Nat}
    {s : TensorStore.Spec}
    (h : tensorStoreTmpl L g t (.cpTensorStore map cs src off policy mode reduce) =
      .tensorStore a s u) :
    tensorStoreSpec L g t map cs src off policy mode reduce = .ok (a, s) ∧ u = next t := by
  simp only [tensorStoreTmpl, ofExec, bind, Except.bind, pure, Except.pure] at h
  rcases hc : tensorStoreSpec L g t map cs src off policy mode reduce with f | ⟨a', s'⟩ <;>
    rw [hc] at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

/-- A successful store specification uses the map at its resolved address: its descriptor
(tile) or the four-row box (scatter4), with row coordinates exactly for scatter4. -/
theorem tensorStoreSpec_ok {L : Launch} {g : Nat} {t : TState} {map : Opnd} {cs : List Opnd}
    {src : Nat} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {a : Nat}
    {s : TensorStore.Spec}
    (h : tensorStoreSpec L g t map cs src off policy mode reduce = .ok (a, s)) :
    tensorMapAddress L g t map = .ok a ∧ ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧
      TensorDescriptor.Valid d ∧ s.descriptor = mode.transfer d ∧
      (s.rows = none ↔ mode = .tile) ∧ s.reduce = reduce := by
  unfold tensorStoreSpec at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  rcases hm : tensorMap L g t map cs mode with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  obtain ⟨hma, hd, hv, -⟩ := tensorMap_ok hm
  dsimp only at h
  repeat' (split at h <;> (try (cases h; done)))
  all_goals
    cases h
    refine ⟨hma, d, hd, hv, rfl, ?_, rfl⟩
    cases mode <;> simp

end
end PTX
