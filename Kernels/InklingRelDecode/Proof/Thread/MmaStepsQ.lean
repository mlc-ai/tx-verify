-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaSiteTac
public import Kernels.InklingRelDecode.Proof.Thread.MmaStepsOv

@[expose] public section

/-! # The MMA warp's steps before the PV half (pc 2422 to 2499)

`site_cases` over the sites with the role's tactics (`MmaSiteTac`), except the sites that read a
word the evaluation does not know (`MmaStepsOv`). The sites from pc 2500 are in `MmaStepsP`;
the two files are checked in parallel. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem stepAt_q (hpre : Pre P L mem0) (tm0 : Nat) (pro0 : Nat → Value) (d : D)
    (hs : d.site.pc < 2500) : (code asms L g tm0 pro0).StepAt d := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  mma_steps s except [.bar0 => ov_bar0 hpre i n tm pro, .qkShfl => ov_qkShfl i n tm pro]
    skip_by (dsimp only at hs; exact absurd hs (by decide))

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
