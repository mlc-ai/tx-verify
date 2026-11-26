-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Lemmas.Flow.Step.SiteIte
public import Kernels.FlashMlaSparseDecodeH64.Gen.StepWg1

@[expose] public section

/-! # Warpgroup 1's segment tactics

The walks after the head shuffle read the parameters; they run with `p0_eq` (`param_0`'s bytes
explicit) in context, which `seg_sym` uses to evaluate the code's `ld.param`s. `w1_seg` closes a
segment by the table's terms. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow

/-- No assumption gives an integer instruction a rule of its own at a pc outside the audited
parameter-pointer, shared-pointer and peer-score sites (`asms_localRule_int`). -/
scoped macro_rules
  | `(tactic| sym_local_none) => `(tactic| (
      intro t ht a ha
      exact asms_localRule_int (t := t) (by rw [ht]; decide) (by rw [ht]; decide)
        (by rw [ht]; decide) (by simp [Assumptions.peerPackRule, Assumptions.peerPack, ht]) a ha))

/-- A branch on a parameter the walk reads as bytes where the table writes `pw`, `pw8`: decided
by the case split's hypothesis up to unfolding. -/
scoped macro_rules
  | `(tactic| sym_decide) => `(tactic| first
      | assumption
      | exact Bool.eq_false_iff.mpr (by assumption))

/-- Warpgroup 1's segments, closed by the table's terms. -/
macro "w1_seg" : tactic => `(tactic| (intro t h; seg_fp h using first | rfl | sym_close))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
