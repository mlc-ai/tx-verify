-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Proof.Correction.LseBase
import Lemmas.Flow.Step.SiteIte
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

/-! # The LSE stores: the first store

The successors of the first LSE store (`lse 0`) on a nonnegative second row sum, by its sign;
otherwise a stop (`StepsLse.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The first LSE store: on a nonnegative second row sum, its successors by the signs of the two
sums; otherwise a stop. -/
theorem stepAt_l0 (hp : Pre p L m) {s : Site} (hs : s = .lse 0) (v : V) :
    (code p L g).StepAt ⟨s, v, 0⟩ := by
  have hparams := params hp
  have hsc := scale_read hp
  have hr0 := readEReal_erealValue_f32 v.rm0.1
  have hr1 := readEReal_erealValue_f32 v.rm1.1
  have hs0 := scale_mul hp v.rm0.1
  have hs1 := scale_mul hp v.rm1.1
  have ht0 := add_log_bot hp v.rm0
  have ht1 := add_log_bot hp v.rm1
  have ha := add_log
  have hm := mul_ln2
  by_cases h1 : 0 ≤ v.rs1
  · rcases h1.lt_or_eq with h1' | h1'
    · have h1n : v.rs1 ≠ 0 := ne_of_gt h1'
      corr_sites s using [h1, h1', ite_true]
    · have hle : v.rs1 ≤ 0 := h1'.ge
      clear h1'
      corr_sites s using [h1, ite_true]
  · subst hs
    exact PTX.Flow.Code.StepAt.of (by site_event (trivial))
      (stop_ok fun e => by simp [succ, h1])

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
