-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasRelease
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasLeader

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Softmax
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Loader
open PTX.Kernels.TmlFa4Fwd.Softmax

/-- An actual Bias-empty update is issued by lane zero of its physical softmax warp. -/
theorem biasReturnLeader {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {i : EvId}
    (hIssue : X.Arrive i (biasEmptyObject l cta stage) 0 1 true .cta) :
    laneOf l i.1 = 0 := by
  obtain ⟨_, he⟩ := hIssue
  exact actualBiasReturnLeader hp hX he (actualBiasEmptyArrivalSite hp hX stage he rfl)

/-- The per-warp Bias return history uses one physical issuer across all visits. -/
theorem biasReturnSameWarpIssuer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {i j : EvId}
    (hi : X.Arrive i (biasEmptyObject l cta stage) 0 1 true .cta)
    (hj : X.Arrive j (biasEmptyObject l cta stage) 0 1 true .cta)
    (hWarp : SameWarp l i.1 j.1) : i.1 = j.1 := by
  have h := sameWarp_lane l hWarp
  rw [biasReturnLeader hp hX stage hi, biasReturnLeader hp hX stage hj,
    Nat.sub_zero, Nat.add_zero] at h
  exact h.symm

end PTX.Kernels.TmlFa4Fwd.Thread.Softmax
