-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderSiteTac

@[expose] public section

/-! # The loader's steps

`site_cases` over the sites with the role's tactics (`LoaderSiteTac`), except the sites whose
steps read a loaded word the evaluation does not know (`step_bar0`: the loop's entry test of the
counter and `num_iters` words; `step_ldb0`, `step_ldb1`: the block-table word, which the code
reads as bits after its load, a word without bits being a fault). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

/-- Every loader state satisfies the code machine's obligation. -/
theorem stepAt (P : Pro) (d : D) : (code L g P).StepAt d := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  site_cases s except [
      .ld0 => ov_ld0 P pro i n p0 p1 ln,
      .ld1 => ov_ld1 P pro i n p0 p1 ln,
      .bar0 => stepOk_of fun hi h hc hf => step_bar0 rfl hi (h.at rfl rfl) hc hf,
      .ldb0 => stepOk_of fun hi h hc hf => step_ldb0 rfl hi (h.at rfl rfl) hc hf,
      .ldb1 => stepOk_of fun hi h hc hf => step_ldb1 rfl hi (h.at rfl rfl) hc hf]
    trans [next]
    seg_by (lw_seg_site)
    inv_by (lw_inv)
    guard_by (lw_guard)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
