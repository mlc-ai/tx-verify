-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Kernel.Progress.Rank
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Table
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time

@[expose] public section

/-! # The following premise of one execution

`Follow P L X`: every launched thread of `X` is followed by the glued thread machine
(`Common/Roles.lean`) with the role table's invariant at each of its events
(`Frame.RoleTable.Followed`, `Common/Table.lean`). It is the name the exports and the classes
above the roles take (`(hFw : Follow P L X)`), without its body: a theorem that takes it does not
read the machine or the role table, so a role lane's change of either rebuilds only the proofs that
open it (`Common/FollowView.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **The thread machine follows every launched thread of `X`.** -/
@[no_expose] def Follow (P : Params) (L : Launch) (X : Execution) : Prop :=
  (table P L).Followed X (fun g => g < L.threads)

/-- **The glued time table** of the progress layer: the thread machine with the time of each
state (`Common/Time.lean`), by name only (its body is `Common/FollowView.lean`'s `timed_eq`). -/
@[no_expose] noncomputable def timed (P : Params) (L : Launch) :
    Sched.Timed kernel Assumptions.all L :=
  ⟨thread P L, time P L⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
