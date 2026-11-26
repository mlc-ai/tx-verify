-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Kernel.NextInOrder

@[expose] public section

/-! # A poll below its time steps under quiet extensions

`Sched.mbar_at_steps` under `Assumption.WfQuiet`. -/

namespace PTX.Sched
open PTX PTX.Flow MBarrier Classical
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

variable {M : Timed K A L}
  {X Y : Execution} {g h : Nat}

/-- **A released thread at an mbarrier wait steps**, when its blockers are earlier than its
time. -/
theorem mbar_at_stepsQ (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A) (hub : ¬ HasUb X)
    (hmax : Maximal L K A mem0 X) (hp : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hne : X.tr g ≠ []) {b : Nat} (h : MbarAt M mem0 X g b) (hb : b < threadTime M X g)
    (h2 : 2 ≤ threadTime M X g) : Steps M mem0 X (.thread g) := by
  obtain ⟨m, pcw, par, Q, before, hpoll, hstate, hB⟩ := h
  refine Descent.mbar_wait_steps_inOrderQ hA hub hmax hp hrel hne hpoll hstate ?_
  intro sc hq hpar hY
  rw [rank_released hrel]
  exact (hB sc hq hpar hY).rank_lt hb h2

end

end PTX.Sched
