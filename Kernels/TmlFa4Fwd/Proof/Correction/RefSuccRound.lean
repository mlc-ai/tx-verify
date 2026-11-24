-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.RefSucc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction machine's successors: the start, the request and the rescale rounds -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
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
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The start. -/
theorem succOk_bar1 : SuccOk p L g .bar1 := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The arrivals of the start. -/
theorem succOk_arr (a : Fin 2) : SuccOk p L g (.arr a) := by
  intro v k e d' h
  fin_cases a <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The request. -/
theorem succOk_q0 : SuccOk p L g .q0 := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The request. -/
theorem succOk_q1 : SuccOk p L g .q1 := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The request. -/
theorem succOk_uk : SuccOk p L g .uk := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The named barriers before the rounds. -/
theorem succOk_nb (a : Fin 2) : SuccOk p L g (.nb a) := by
  intro v k e d' h
  fin_cases a <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The arrival between them. -/
theorem succOk_free : SuccOk p L g .free := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The named barrier of a round. -/
theorem succOk_rbar (st : Fin 2) : SuccOk p L g (.rbar st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The scale of a round. -/
theorem succOk_rscale (st : Fin 2) : SuccOk p L g (.rscale st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The ballot of a round. -/
theorem succOk_rvote (st : Fin 2) : SuccOk p L g (.rvote st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- A rescale load. -/
theorem succOk_rld (st : Fin 2) (c : Fin 8) : SuccOk p L g (.rld st c) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The wait of a rescale load. -/
theorem succOk_rldw (st : Fin 2) (c : Fin 8) : SuccOk p L g (.rldw st c) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- A rescale store. -/
theorem succOk_rst (st : Fin 2) (c : Fin 8) : SuccOk p L g (.rst st c) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The store wait of a round. -/
theorem succOk_rwait (st : Fin 2) : SuccOk p L g (.rwait st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The arrivals of a round. -/
theorem succOk_rarr (st b : Fin 2) : SuccOk p L g (.rarr st b) := by
  intro v k e d' h
  fin_cases st <;> fin_cases b <;> sc_split
  all_goals sc_close

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
