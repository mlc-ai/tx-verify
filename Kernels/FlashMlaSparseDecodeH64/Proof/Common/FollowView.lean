-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Table
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import all Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow

@[expose] public section

/-! # The body of the following premise

For a role's export (or `Common/`) that opens `Follow`: it is the role table's following of every
launched thread (it reads the body through `import all`, which only `Common/` may use).
Files above `Common/` do not import this file. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

theorem follow_iff {P : Params} {L : Launch} {X : Execution} :
    Follow P L X ↔ (table P L).Followed X (fun g => g < L.threads) :=
  Iff.rfl

/-- The glued time table is the thread machine with `time`. -/
theorem timed_eq {P : Params} {L : Launch} : timed P L = ⟨thread P L, time P L⟩ := by
  unfold timed
  rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
