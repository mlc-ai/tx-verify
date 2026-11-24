-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Lemmas.Flow.NotAsyncWait
public import Lemmas.Protocol.CpAsyncCompletionOrder
public import Lemmas.Protocol.CpAsyncArriveOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow

private theorem noAsyncWaitCode : kernel.code.all (fun i => !asyncWaitOp i.op) = true := by
  decide +kernel

/-- KV vectors use arrive-on to report availability. The bulk waits cover output stores. -/
theorem noCopyGroupWait {A : List Assumption} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {s : AsyncCopy.Spec} (hCopy : X.Copy i s) :
    ∀ k w, ¬ GroupWaitsFor X k i w := by
  intro k w
  cases k with
  | bulk mode =>
    exact not_bulkWaitsFor_of_copy hCopy (by rw [(actualCopyShape hX hCopy).completion]; decide)
  | cpAsync =>
    rintro ⟨pc, n, he, _⟩
    exact no_kind_of_code hX asyncWaitOp (fun kind => ∃ n, kind = .asyncWait n)
      (fun _ ⟨_, h⟩ => by cases h)
      (fun hf ⟨_, hk⟩ => fires_asyncWait_op hf hk) noAsyncWaitCode he ⟨n, rfl⟩

end PTX.Kernels.TmlFa4Fwd.Loader
