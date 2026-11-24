-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputActualSources
public import Kernels.TmlFa4Fwd.Proof.LoaderExpectTx
public import Lemmas.Protocol.ObjectSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX

/-- Every performed transaction-byte completion retires exactly one Q or Bias subbox. -/
theorem completedInputBytes {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {target : Loc} {r : MBarrier.Record AsyncCopy.Ref} {bytes : Nat}
    (hr : r ∈ X.objects target) (ha : r.action = .completeTx bytes) :
    bytes = 16384 := by
  cases AsyncCopy.record_source hX.tma.2.2.1 hr
  case tensor _ he _ hRecord =>
    have hb := MBarrier.Action.completeTx.inj (ha.symm.trans hRecord)
    exact hb.trans (actualTensorInputTxBytes hp hX ⟨_, he⟩)
  case bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  case clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim
  all_goals simp_all

end PTX.Kernels.TmlFa4Fwd.Protocol
