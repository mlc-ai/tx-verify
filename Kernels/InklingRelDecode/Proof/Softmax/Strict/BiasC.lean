-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Bias
public import Lemmas.Flow.TypedIntG
import Kernels.InklingRelDecode.Flow.Code
@[expose] public section
/-! # The strict step of the loop's bias loads: the checks of the tables (pcs 1124 to 1250) -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g i : Nat} {v : Control.Carry} {w : Data.Vals}

theorem nxt_aft : ∀ j < 63,
    afterF lateQt (1124 + 2 * j) [] = true := by
  decide +kernel

theorem nxt_nk : ∀ j < 63, (if j = 0 then 332 else 333 + j) ∉
    (lateQt (1124 + 2 * j + 1)).map Prod.fst := by
  decide +kernel


theorem nxt_mv : ∀ j < 63, checkW absF5 lateQt (1124 + 2 * j + 1) (1124 + 2 * j + 2)
    ((kernel.code.drop (1124 + 2 * j + 1)).take (1124 + 2 * j + 2 - (1124 + 2 * j + 1)))
      [334 + j] = true := by
  decide +kernel


theorem nxt_last_aft : afterF lateQt 1250 [] = true := by decide +kernel

theorem nxt_last_nk : 396 ∉ (lateQt 1251).map Prod.fst := by decide +kernel


end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
