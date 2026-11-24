-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.ProgressSources
public import Lemmas.Step.CtaBarArrive
public import Kernels.FlashAttn4Fwd.Proof.Polls.Waits
public import Kernels.FlashAttn4Fwd.Proof.ProgressNextGlue

@[expose] public section

/-! # ProgressGoal from the safety goal (draft)

This file sits at the top of the proof tree, outside the layer order: it instantiates the
progress assembly with the protocol exports and the facts of the whole execution at a thread's
next event (`nextSafe`, `ProgressNextGlue.lean`). Draft: `progress_goal` takes the premises not
supplied yet as `Progress.Remaining`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **ProgressGoal (draft).** Every maximal execution is complete, given the safety goal and
the remaining premises, and the order of the conflicts outside O (from the safety layer,
`Safety.outside_ordered`). -/
theorem progress_goal (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hR : Progress.Remaining L mem0)
    (hord : ∀ X, Consistent L kernel asms mem0 X →
      ConflictsOrdered L X fun l => ¬ Safety.InTensor P P.oBase P.sq l) :
    ProgressGoal kernel asms L mem0 :=
  Progress.progress_of_remaining hR (asyncSources hpre hR) (nextSafe hpre hs hR hord)
    (Progress.pollsBlocked hpre hs (fun X hX => hR.async P X hpre hX) hR.waits hR.polls
      (fun X hX => hR.pollInputs P X hpre hX)) (fun _ hX => tracked hpre hX) hpre hs

end

end PTX.Kernels.FlashAttn4Fwd.Proof
