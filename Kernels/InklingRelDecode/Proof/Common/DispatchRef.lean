-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Dispatch.Rounds

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

/-- A lane that has called no role has made no poll of the two loops and no final collective. -/
def noWorkerPolls (n : Cls → Nat) :=
  n (.poll 2374) = 0 ∧ n (.poll 2462) = 0 ∧ n (.poll 2510) = 0 ∧
    n (.atPc 2550) + n (.atPc 2551) = 0

/-- **What a dispatch state knows of the counts** (`lo`, `hi` the loader's and the MMA's bounds):
in the first round nothing was polled; in a later round the role has returned, so the loader has
made every poll, the MMA warp every poll and both final collectives. -/
def DispatchRef (warp lo hi : Nat) (d : Dispatch.D) (n : Cls → Nat) : Prop :=
  Dispatch.Allowed d ∧ Dispatch.Busy warp d ∧ (d.round = 0 → noWorkerPolls n) ∧
    (d.round ≠ 0 → (warp = 6 → n (.poll 2374) = hi - lo) ∧
      (warp = 7 → n (.poll 2462) = Mma.runCount hi ∧ n (.poll 2510) = Mma.runCount hi ∧
        n (.atPc 2550) + n (.atPc 2551) = 2))

end PTX.Kernels.InklingRelDecode.Proof
