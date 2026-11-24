-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.NotBulkPrefetch
public import Lemmas.Flow.NotTensorPrefetch
public import Lemmas.Flow.StoreValid

@[expose] public section

/-! # The forms of the tensor prefetches and stores, from the code

Static scans of the decoded code: no tensor prefetch is issued, and every tensor store is a valid
tile write without a reduction. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Flow

private theorem noTensorPrefetchCode :
    kernel.code.all (fun i => !tensorPrefetchOp i.op) = true := by
  decide +kernel

/-- The startup prefetches are of map descriptors; no tensor element prefetch is issued. -/
theorem noTensorPrefetch {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {address : Nat} {s : TensorPrefetch.Spec}
    (hi : X.TensorPrefetchIssue i address s) : False := by
  obtain ⟨_, he⟩ := hi
  exact no_kind_of_code hX tensorPrefetchOp (fun k => ∃ address s, k = .tensorPrefetch address s)
    (fun _ ⟨_, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, hk⟩ => fires_tensorPrefetch_op hf hk) noTensorPrefetchCode he ⟨_, _, rfl⟩

private def plainTileStore : Op → Bool
  | .cpTensorStore _ _ _ _ _ .tile none => true
  | op => !tensorStoreOp op

private theorem plainTileStoreCode : kernel.code.all (fun i => plainTileStore i.op) = true := by
  decide +kernel

/-- Every issued output store resolves to a valid tile write without a reduction. -/
theorem actualTensorStoreForm {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {addr : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue i addr s) :
    TensorStore.Valid (i.1 / l.block) s ∧ s.rows = none ∧ s.reduce = none := by
  obtain ⟨_, he⟩ := hi
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hf
  have hop := fires_tensorStore_op hf rfl
  have hs := List.all_eq_true.mp plainTileStoreCode ins (List.mem_of_getElem? hCode)
  cases hIns : ins.op <;> simp only [hIns, tensorStoreOp, Bool.false_eq_true] at hop
  case cpTensorStore map cs r off policy mode reduce =>
    cases mode <;> cases reduce <;> simp [hIns, plainTileStore, tensorStoreOp] at hs
    rw [hIns] at hf
    exact fires_cpTensorStore_form hf addr s rfl

end PTX.Kernels.TmlFa4Fwd.Proof
