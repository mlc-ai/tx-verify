-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbId
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbRole
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles

@[expose] public section

/-! # The vocabulary of the undefined-behaviour leaves

The lane's state before an event, by role, and the machine's death after the event, named without
the state: `RoleId` lists the roles of the thread machine, `AliveIn P L X g k r` says the thread's
machine is at a state of role `r` before its `k`-th event, `StopsAt` that it stops at that event.
`NoUbLeaf` is the obligation a role owes `Safe.noUb`: an event fired from a state of the role is no
undefined behaviour (`safe`), and the machine stops at it only if it is an exit (`live`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

/-- **The thread's machine is at a state of role `r` before event `k`.** -/
@[no_expose] def AliveIn (P : Params) (L : Launch) (X : Execution) (g k : Nat) (r : RoleId) :
    Prop :=
  ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ) ∧ InRole P L g r σ

/-- **The thread's machine stops at event `k`** (it has no successor state). -/
@[no_expose] def StopsAt (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  Frame.stateAt (thread P L) X g (k + 1) = none

/-- **What a role owes `Safe.noUb`**: an event of a followed lane, fired from a state of the
role, is no undefined behaviour, and the machine stops at it only if it is an exit. -/
def NoUbLeaf (P : Params) (L : Launch) (m : Mem0) (r : RoleId) : Prop :=
  Pre P L m → ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X →
    ∀ g k e, X.get (g, k) = some e → AliveIn P L X g k r →
      (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
