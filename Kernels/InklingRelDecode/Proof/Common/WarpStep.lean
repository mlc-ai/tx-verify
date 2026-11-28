-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.WarpColl
public import Lemmas.Quiet.Progress.ReleasedG
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Common.DataColl
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import all Kernels.InklingRelDecode.Proof.Common.Follow
import all Kernels.InklingRelDecode.Proof.Common.Time

@[expose] public section

/-! # A released lane at a warp collective steps

The library's step at a warp collective (`Sched.warpColl_steps_relK`) for the code, which has no
ballot, from the facts of the pairs of lanes of each warp (`Sched.WarpPair`): every lane of a
warp is launched, none is canceled, and the extensions append events that read no memory. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Descent

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem no_ballot : kernel.code.all (fun ins => !Sched.ballotOp ins.op) = true := by
  decide +kernel

/-- **A released pending lane at a warp collective steps.** -/
theorem warp_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hc : NextEnvG L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hpairs : ∀ {g h : Nat}, SameWarp L g h →
      Sched.WarpPair m (schedule Q L) X (CollAt Q L) (collS Q L) g h)
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    {d : ((schedule Q L).code g).D}
    (hσ : Frame.stateAt (schedule Q L).code X g (X.tr g).length = some (some d))
    (hat : CollAt Q L g d) : Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hc.max.1
  have hlaunch : ∀ h, Step.Launched L X h := fun _ ⟨_, _, _, ⟨_, hi⟩⟩ => (Lib.no_clc hX hi).elim
  have hcl : ∀ h, ¬ ClcCanceled L X h := by
    rintro h ⟨-, r, hr⟩
    obtain ⟨i, s, ts, -, ⟨pc, hi⟩, -⟩ := hX.clc.canceled_has_issue hr
    exact Lib.no_clc hX hi
  have ht : Frame.Tracked (schedule Q L).code X := fun h k hh => (hf h hh k).1
  exact Sched.warpColl_steps_relK no_ballot (fun hsw => warpKey_eq hsw)
    (fun _ hg => thread_sound hp hg) hs ht (warp_rel hp hX hpairs)
    (by rw [hp.block]) hlaunch hcl
    (fun ds ev h a ha => Lib.assumptions_step _ _ hX le_appendLanes
      (Execution.notifiedInOrder_of_eq rfl) (noNewRead_appendLanes h) a ha)
    (fun hh hrl hrun hl hout => Step.plain_counted_extension hX hh (.inr (hlaunch _)) hrl hrun hl
      (o := none) ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
      (hX.tmemPairResult.snoc_not_wr nofun) (hc.snoc_wf rfl))
    hc.max hpd hσ hat hrel

end PTX.Kernels.InklingRelDecode.Proof
