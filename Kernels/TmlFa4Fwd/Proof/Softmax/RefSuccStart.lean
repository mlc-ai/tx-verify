-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.RefSucc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax machine's successors: the start, the request, the final stores and the end -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The start. -/
theorem succOk_setmax : SuccOk p L g .setmax := by
  intro v k acc e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The start's barrier. -/
theorem succOk_bar1 : SuccOk p L g .bar1 := by
  intro v k acc e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The request. -/
theorem succOk_q0 : SuccOk p L g .q0 := by
  intro v k acc e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The request. -/
theorem succOk_q1 : SuccOk p L g .q1 := by
  intro v k acc e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The request. -/
theorem succOk_uk : SuccOk p L g .uk := by
  intro v k acc e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The first round's extra poll. -/
theorem succOk_wq : SuccOk p L g .wq := by
  intro v k acc e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The final stores. -/
theorem succOk_fin (j : Fin 2) : SuccOk p L g (.fin j) := by
  intro v k acc e d' h
  fin_cases j <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The final arrival. -/
theorem succOk_finarr : SuccOk p L g .finarr := by
  intro v k acc e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The end's poll. -/
theorem succOk_wend (l : Bool) : SuccOk p L g (.wend l) := by
  intro v k acc e d' h
  cases l <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The end's barrier. -/
theorem succOk_barEnd (l : Bool) : SuccOk p L g (.barEnd l) := by
  intro v k acc e d' h
  cases l <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The exit. -/
theorem succOk_exit (l : Bool) : SuccOk p L g (.exit l) := by
  intro v k acc e d' h
  cases l <;> sc_split
  all_goals sc_close

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
