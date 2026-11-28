-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode

@[expose] public section

/-! # The side conditions of a warp-level step

Two of the facts the library's warp progress lemmas ask of the kernel besides its own relation: no
lane waits for a launch and no lane is canceled (the code issues no cluster launch control
request). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {L : Launch} {m : Mem0} {X : Execution}

/-- Every thread is launched. -/
theorem launched_all (hX : Consistent L kernel Assumptions.all m X) :
    ∀ h, Step.Launched L X h := fun _ ⟨_, _, _, hi⟩ => (noClcIssue hX hi).elim

/-- No thread is canceled. -/
theorem noCanceled (hX : Consistent L kernel Assumptions.all m X) :
    ∀ h, ¬ ClcCanceled L X h := by
  rintro h ⟨-, r, hr⟩
  obtain ⟨i, s, ts, -, ⟨pc, hi⟩, -⟩ := hX.clc.canceled_has_issue hr
  exact noClcIssue hX ⟨pc, hi⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
