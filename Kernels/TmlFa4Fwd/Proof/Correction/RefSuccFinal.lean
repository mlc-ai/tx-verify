-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.RefSucc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction machine's successors: the final stage, the LSE and the end -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The first arrival of the final stage. -/
theorem succOk_farr0 : SuccOk p L g .farr0 := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The named barrier of a final stage. -/
theorem succOk_fbar (st : Fin 2) : SuccOk p L g (.fbar st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- A row-sum read. -/
theorem succOk_fsum (st : Fin 2) : SuccOk p L g (.fsum st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- A row-maximum read. -/
theorem succOk_fmax (st : Fin 2) : SuccOk p L g (.fmax st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The arrival of a final stage. -/
theorem succOk_farr (st : Fin 2) : SuccOk p L g (.farr st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The polls of a final stage. -/
theorem succOk_fw (st b : Fin 2) : SuccOk p L g (.fw st b) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- A final load. -/
theorem succOk_fld (st : Fin 2) (j : Fin 16) : SuccOk p L g (.fld st j) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The wait of a final load. -/
theorem succOk_fwl (st : Fin 2) (j : Fin 16) : SuccOk p L g (.fwl st j) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The elements of a final store. -/
theorem succOk_fst (st : Fin 2) (j : Fin 16) (b : Fin 2) : SuccOk p L g (.fst st j b) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The fence of a final stage. -/
theorem succOk_fence (st : Fin 2) : SuccOk p L g (.fence st) := by
  intro v k e d' h
  sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The last arrivals of a final stage. -/
theorem succOk_fdone (st b : Fin 2) : SuccOk p L g (.fdone st b) := by
  intro v k e d' h
  fin_cases st <;> fin_cases b <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The LSE stores. -/
theorem succOk_lse (a : Fin 2) : SuccOk p L g (.lse a) := by
  intro v k e d' h
  fin_cases a <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The poll of the end. -/
theorem succOk_wend (l : Bool) : SuccOk p L g (.wend l) := by
  intro v k e d' h
  cases l <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The barrier of the end. -/
theorem succOk_barEnd (l : Bool) : SuccOk p L g (.barEnd l) := by
  intro v k e d' h
  cases l <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The exit. -/
theorem succOk_exit (l : Bool) : SuccOk p L g (.exit l) := by
  intro v k e d' h
  cases l <;> sc_split
  all_goals sc_close

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
