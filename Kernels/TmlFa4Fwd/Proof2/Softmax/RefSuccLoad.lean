-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.RefSucc

@[expose] public section

/-! # The softmax machine's successors: the score and bias loads -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The score polls. -/
theorem succOk_ws (r : Rd) : SuccOk p L g (.ws r) := by
  intro v k acc e d' h
  cases r <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The score loads. -/
theorem succOk_sld (r : Rd) (c : Fin 4) : SuccOk p L g (.sld r c) := by
  intro v k acc e d' h
  cases r <;> fin_cases c <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The implicit waits of a plain round's score loads. -/
theorem succOk_sldw (c : Fin 4) : SuccOk p L g (.sldw c) := by
  intro v k acc e d' h
  fin_cases c <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The bias polls. -/
theorem succOk_wb (b : Bool) : SuccOk p L g (.wb b) := by
  intro v k acc e d' h
  cases b <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The bias loads. -/
theorem succOk_bld (b : Bool) (c : Fin 16) : SuccOk p L g (.bld b c) := by
  intro v k acc e d' h
  cases b <;> fin_cases c <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The proxy fences. -/
theorem succOk_fence (b : Bool) : SuccOk p L g (.fence b) := by
  intro v k acc e d' h
  cases b <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The stage's named barrier. -/
theorem succOk_bsync (b : Bool) : SuccOk p L g (.bsync b) := by
  intro v k acc e d' h
  cases b <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The arrival freeing the bias slot. -/
theorem succOk_barr (b : Bool) : SuccOk p L g (.barr b) := by
  intro v k acc e d' h
  cases b <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The statistics stores. -/
theorem succOk_stat (b : Bool) : SuccOk p L g (.stat b) := by
  intro v k acc e d' h
  cases b <;> sc_split
  all_goals sc_close

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
