-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QUtccpPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QUtccpRestPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Tc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.DequantReadyPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.ClosePoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.RawFreePoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.SoReadyPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QkDonePoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.SvDonePoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.RawReadyPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.CoordReadyPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.CoordFreePoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Other
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Store
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Tensor
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Tmem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Blocked
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Quiet
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietIndex
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietWg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietMma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietStartup
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietWg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.NextRow
public import Lemmas.Kernel.Descent
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll

@[expose] public section

/-! # The progress assembly: every open obligation steps

`ProgressGoal` given safety, by ranked descent (`Descent.progress_of_steps` with the glued time
table's rank `Sched.rank (timed P L)`). An open obligation of a maximal execution is of one class
(`Top/Prog/Classes.lean`), found by the next event of a lane only:

* a pending lane that is not released is blocked by its last event (`Prog.blocked`);
* a pending released lane steps, or its next event is a failed poll (`next_cls`, from
  `Prog.nextRow`); the poll's pc is one of the sixteen waits (`poll_pcs`), whose channel's class
  steps it (`Prog.sites_cls`): every class is proved from the inputs (`Prog.qTmaPoll`,
  `Prog.qUtccpMmaPoll`, `Prog.dequantReadyPoll`, `Prog.closePoll`, `Prog.rawFreePoll`,
  `Prog.soReadyPoll`, `Prog.rawReadyPoll`, `Prog.qUtccpRestPoll`, `Prog.coordReadyPoll`,
  `Prog.coordFreePoll`, `Prog.qkDonePoll`, `Prog.svDonePoll`);
* an asynchronous obligation is of its class (`tensor`, `tc`, `store`, `tmem`, `other`; `other`
  and `tmem` are proved, `Prog.other`, `Prog.tmem`; `store` from the stores' publication,
  `Prog.store`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **A failed poll steps**, by its channel. -/
theorem Prog.poll_steps (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hF : ∀ X, Consistent L kernel Assumptions.all mem0 X → Follow P L X)
    (hs : SafeGoal kernel Assumptions.all L mem0)
    {X : Execution} (hmax : Maximal L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {g pc : Nat} (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hf : FailsAt L mem0 X g pc) : Sched.Steps (timed P L) mem0 X (.thread g) := by
  obtain ⟨_, _, _, Y, hY, -, he⟩ := id hf
  rcases Prog.sites_cls (poll_pcs hY he) with h | h | h | h | h | h | h | h | h | h | h
  · exact Prog.qTmaPoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.qUtccpMmaPoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.qUtccpRestPoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · rcases Prog.coord_split h with h | h
    · exact Prog.coordReadyPoll hp hIn hF hs X hmax hFw h hpd hrel hf
    · exact Prog.coordFreePoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.qkDonePoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.svDonePoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.dequantReadyPoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.soReadyPoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.closePoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.rawFreePoll hp hIn hF hs X hmax hFw h hpd hrel hf
  · exact Prog.rawReadyPoll hp hIn hF hs X hmax hFw h hpd hrel hf

/-- **Every open obligation of a maximal execution steps.** -/
theorem Prog.obl_steps (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hF : ∀ X, Consistent L kernel Assumptions.all mem0 X → Follow P L X)
    (hs : SafeGoal kernel Assumptions.all L mem0) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all mem0 X) (hFw : Follow P L X)
    {o : Descent.Obligation} (ho : Descent.Obl L X o) : Sched.Steps (timed P L) mem0 X o := by
  cases o with
  | thread g =>
    by_cases hrel : Step.Released L X g
    · have hpub := Prog.storePub hp fun X hX hFw => hIn.bar hp X hX hFw
      rcases next_cls hp hFw (Prog.nextRow hIn hp hpub X) (Prog.tail hp hpub X)
        (Prog.dequantRow hIn hp hpub X) (Prog.indexRow hIn hp hpub X)
        (Prog.tmaRow hIn hp hpub X)
        (Prog.wg1Row hIn hp hpub X)
        (Prog.mmaRow hIn hp hpub X) (Prog.wg0Row hIn hp hpub X)
        (Prog.startupRow hIn hp hpub X) hs hmax ho hrel
        with h | ⟨pc, hf⟩
      · exact h
      · exact Prog.poll_steps hp hIn hF hs hmax hFw ho hrel hf
    · exact Prog.blocked hp hIn hs X hmax hFw ho hrel
  | tensor => exact Prog.tensor hp hs X hmax hFw _ (by simp) ho
  | mma => exact Prog.tc hp hIn hs X hmax hFw _ (by simp) ho
  | commit => exact Prog.tc hp hIn hs X hmax hFw _ (by simp) ho
  | store =>
    exact Prog.store (Prog.storePub hp (fun X hX hFw => hIn.bar hp X hX hFw)) hs X
      hmax hFw _ (by simp) ho
  | tmem => exact Prog.tmem hp hIn hs X hmax hFw _ (by simp) ho
  | bulk => exact Prog.other hs X hmax hFw _ (by simp) ho
  | arriveOn => exact Prog.other hs X hmax hFw _ (by simp) ho
  | clc => exact Prog.other hs X hmax hFw _ (by simp) ho

/-- **Progress by ranked descent**, given safety. -/
theorem progress (hp : Pre P L mem0)
    (hs : SafeGoal kernel Assumptions.all L mem0) : ProgressGoal kernel Assumptions.all L mem0 :=
  Descent.progress_of_steps (Descent.Obl L) (Sched.rank (timed P L))
    (fun _ _ hc => Descent.cover hc) fun X _ hmax ho' =>
      Prog.obl_steps hp (Inputs.of_pre hp) (follow_of hp) hs hmax (follow_of hp X hmax.1) ho'

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
