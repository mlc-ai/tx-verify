-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Pointers
import Kernels.InklingRelDecode.Gen.StepSoftmax01
import Kernels.InklingRelDecode.Gen.StepSoftmax02
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {d : D}
local notation "F" => facts e L g d

private theorem preptr_615 :
    SegU kernel Assumptions.all L g 615 (F 615) 616 (F 616) := by
  apply SegU.of_seg (n := 1)
  intro t ht
  seg_fp ht using exact ptr_mad _ _

local macro "offsets" n:num : tactic => `(tactic| (
  apply SegU.of_seg (n := $n)
  intro t ht
  seg_fp ht using exact ptr_add _ _))

private theorem preptr_616 : SegU kernel Assumptions.all L g 616 (F 616)
    623 (F 623) := by offsets 7

private theorem preptr_623 : SegU kernel Assumptions.all L g 623 (F 623)
    630 (F 630) := by offsets 7

private theorem preptr_630 : SegU kernel Assumptions.all L g 630 (F 630)
    637 (F 637) := by offsets 7

private theorem preptr_637 : SegU kernel Assumptions.all L g 637 (F 637)
    644 (F 644) := by offsets 7

private theorem preptr_644 : SegU kernel Assumptions.all L g 644 (F 644)
    651 (F 651) := by offsets 7

private theorem preptr_651 : SegU kernel Assumptions.all L g 651 (F 651)
    658 (F 658) := by offsets 7

private theorem preptr_658 : SegU kernel Assumptions.all L g 658 (F 658)
    665 (F 665) := by offsets 7

private theorem preptr_665 : SegU kernel Assumptions.all L g 665 (F 665)
    672 (F 672) := by offsets 7

private theorem preptr_672 : SegU kernel Assumptions.all L g 672 (F 672)
    679 (F 679) := by offsets 7

private theorem preptr_679 : SegU kernel Assumptions.all L g 679 (F 679) 680 (F 680) := by
  seg_ctl Lib.rulesFrame, Lib.hooks_ok

theorem pre_pointers : SegU kernel Assumptions.all L g 615 (F 615) 680 (F 680) := by
  apply preptr_615.comp
  apply preptr_616.comp
  apply preptr_623.comp
  apply preptr_630.comp
  apply preptr_637.comp
  apply preptr_644.comp
  apply preptr_651.comp
  apply preptr_658.comp
  apply preptr_665.comp
  apply preptr_672.comp
  exact preptr_679

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
