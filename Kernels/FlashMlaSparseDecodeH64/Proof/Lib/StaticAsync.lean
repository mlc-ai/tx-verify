-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # No `cp.async.mbarrier.arrive`

A static scan of the decoded program, evaluated once (`decide +kernel`): no instruction is a
`cp.async.mbarrier.arrive`, so no event of a consistent execution is an asynchronous arrive-on
(`noAsyncArrive`), by the library's code check `no_kind_of_code`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

private theorem noAsyncArriveCode : kernel.code.all (fun ins => !asyncArriveOp ins.op) = true := by
  decide +kernel

/-- No asynchronous arrive-on is issued. -/
theorem noAsyncArrive (hX : Consistent l kernel A m X) {i : EvId} {lc : Loc} {noinc : Bool}
    (h : X.AsyncArrive i lc noinc) : False := by
  obtain ⟨_, he⟩ := h
  exact no_kind_of_code hX asyncArriveOp (fun k => ∃ lc noinc, k = .asyncArrive lc noinc)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_asyncArrive_op hf hk)
    noAsyncArriveCode he ⟨_, _, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
