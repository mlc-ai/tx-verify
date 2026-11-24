-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.RefSucc

@[expose] public section

/-! # The correction machine's successors: the scheduler -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The reads of the scan. -/
theorem succOk_word (sk : Epilogue.Scan) : SuccOk p L g (.word sk) := by
  intro v k e d' h
  cases sk <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The first shuffles of the scan. -/
theorem succOk_down (sk : Epilogue.Scan) : SuccOk p L g (.down sk) := by
  intro v k e d' h
  cases sk <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The prefix shuffles of the scan. -/
theorem succOk_up (sk : Epilogue.Scan) (j : Fin 5) : SuccOk p L g (.up sk j) := by
  intro v k e d' h
  cases sk <;> fin_cases j <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The totals of the scan. -/
theorem succOk_total (sk : Epilogue.Scan) : SuccOk p L g (.total sk) := by
  intro v k e d' h
  cases sk <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The ballots. -/
theorem succOk_vote (l : Bool) : SuccOk p L g (.vote l) := by
  intro v k e d' h
  cases l <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The chosen prefixes. -/
theorem succOk_pre (l : Bool) : SuccOk p L g (.pre l) := by
  intro v k e d' h
  cases l <;> sc_split
  all_goals sc_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- The tile counts. -/
theorem succOk_tiles (l : Bool) : SuccOk p L g (.tiles l) := by
  intro v k e d' h
  cases l <;> sc_split
  all_goals sc_close

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
