-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The counts at the scheduler's, the request's and the end's sites and the quiet pipeline
sites -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the scheduler's scan. -/
theorem step_word (_hp : Pre p L m) (sk : Epilogue.Scan) : StepRef p L g (.word sk) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  cases sk <;> simp only [Ev, Site.toE, Epilogue.Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, word32, scAt, afterTotal, loopHead, scanExit, reduceCtorEq,
      Bool.false_eq_true, ↓reduceIte] at hn <;>
    repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the scheduler's scan. -/
theorem step_down (_hp : Pre p L m) (sk : Epilogue.Scan) : StepRef p L g (.down sk) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  cases sk <;> simp only [Ev, Site.toE, Epilogue.Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, word32, scAt, afterTotal, loopHead, scanExit, reduceCtorEq,
      Bool.false_eq_true, ↓reduceIte] at hn <;>
    repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the scheduler's scan. -/
theorem step_up (_hp : Pre p L m) (sk : Epilogue.Scan) (j : Fin 5) : StepRef p L g (.up sk j) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  cases sk <;> simp only [Ev, Site.toE, Epilogue.Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, word32, scAt, afterTotal, loopHead, scanExit, reduceCtorEq,
      Bool.false_eq_true, ↓reduceIte] at hn <;>
    repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the scheduler's scan. -/
theorem step_total (_hp : Pre p L m) (sk : Epilogue.Scan) : StepRef p L g (.total sk) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  cases sk <;> simp only [Ev, Site.toE, Epilogue.Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, word32, scAt, afterTotal, loopHead, scanExit, reduceCtorEq,
      Bool.false_eq_true, ↓reduceIte] at hn <;>
    repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across the tile count's broadcast. -/
theorem step_tiles (_hp : Pre p L m) (l : Bool) : StepRef p L g (.tiles l) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  cases l <;> simp only [Ev, Site.toE, Epilogue.Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at hn <;> split at hn
  all_goals first | (cases hn; done) | skip
  · obtain ⟨s', v'⟩ := d'
    obtain ⟨h, hps⟩ := afterTiles_ord hn
    simp only at h hps
    exact refc_quiet hQ (by simp [quietK]) (by rw [h]; decide) (by rw [h]; decide)
      (fun h => by simp [Site.ord] at h) hps
  · rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across the ballot and the chosen prefix. -/
theorem step_vote (_hp : Pre p L m) (l : Bool) : StepRef p L g (.vote l) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  cases l <;> simp only [Ev, Site.toE, Epilogue.Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, word32, scAt, afterTiles, Option.map, reduceCtorEq, Bool.false_eq_true,
      ↓reduceIte] at hn <;>
    repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across the ballot and the chosen prefix. -/
theorem step_pre (_hp : Pre p L m) (l : Bool) : StepRef p L g (.pre l) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  cases l <;> simp only [Ev, Site.toE, Epilogue.Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, word32, scAt, afterTiles, Option.map, reduceCtorEq, Bool.false_eq_true,
      ↓reduceIte] at hn <;>
    repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step before the pipeline. -/
theorem step_bar1 (_hp : Pre p L m) : StepRef p L g (.bar1) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, word32, scAt, passStart, reduceCtorEq, Bool.false_eq_true,
    ↓reduceIte] at hn
  all_goals repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step before the pipeline. -/
theorem step_ldAlloc (_hp : Pre p L m) : StepRef p L g (.ldAlloc) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, word32, scAt, passStart, reduceCtorEq, Bool.false_eq_true,
    ↓reduceIte] at hn
  all_goals repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step before the pipeline. -/
theorem step_bcast (_hp : Pre p L m) : StepRef p L g (.bcast) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, word32, scAt, passStart, reduceCtorEq, Bool.false_eq_true,
    ↓reduceIte] at hn
  all_goals repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step before the pipeline. -/
theorem step_q0 (_hp : Pre p L m) : StepRef p L g (.q0) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, word32, scAt, passStart, reduceCtorEq, Bool.false_eq_true,
    ↓reduceIte] at hn
  all_goals repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step before the pipeline. -/
theorem step_q1 (_hp : Pre p L m) : StepRef p L g (.q1) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, word32, scAt, passStart, reduceCtorEq, Bool.false_eq_true,
    ↓reduceIte] at hn
  all_goals repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step before the pipeline. -/
theorem step_uk (_hp : Pre p L m) : StepRef p L g (.uk) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, word32, scAt, passStart, reduceCtorEq, Bool.false_eq_true,
    ↓reduceIte] at hn
  all_goals repeat' split at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the end. -/
theorem step_relinq (_hp : Pre p L m) (l : Bool) : StepRef p L g (.relinq l) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals cases l
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the end. -/
theorem step_bar2 (_hp : Pre p L m) (l : Bool) : StepRef p L g (.bar2 l) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals cases l
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the end. -/
theorem step_dealloc (_hp : Pre p L m) (l : Bool) : StepRef p L g (.dealloc l) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals cases l
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a step of the end. -/
theorem step_exit (_hp : Pre p L m) (l : Bool) : StepRef p L g (.exit l) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  all_goals cases l
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals simp only [succ, reduceCtorEq] at hn
  all_goals first | (cases hn; done) | rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a broadcast or an MMA of the pipeline. -/
theorem step_sh (_hp : Pre p L m) (k : Fin 14) : StepRef p L g (.sh k) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  fin_cases k <;> simp only [Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, word32, reduceCtorEq] at hn <;> repeat' split at hn
  all_goals first | (cases hn; done) | skip
  all_goals simp only [Option.some.injEq] at hn
  all_goals subst hn
  all_goals exact refc_sh _ hQ rfl

set_option maxHeartbeats 4000000 in
/-- The counts across a broadcast or an MMA of the pipeline. -/
theorem step_qk (_hp : Pre p L m) (b : Fin 4) (j : Fin 8) : StepRef p L g (.qk b j) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  fin_cases b <;> simp only [Ev] at hev <;> shape_destruct hev <;> simp only [succ] at hn <;>
    split at hn
  all_goals rq_quiet

set_option maxHeartbeats 4000000 in
/-- The counts across a broadcast or an MMA of the pipeline. -/
theorem step_pv (_hp : Pre p L m) (b : Fin 4) (j : Fin 8) : StepRef p L g (.pv b j) := by
  intro v n r w pc kd d' hQ hE hev hub hn
  fin_cases b <;> fin_cases j <;> simp only [Ev] at hev <;> shape_destruct hev <;>
    simp only [succ, Fin.isValue, Fin.reduceFinMk] at hn
  all_goals rq_quiet


end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
