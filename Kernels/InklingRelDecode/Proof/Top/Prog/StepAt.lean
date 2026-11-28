-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.ReadStep
public import Kernels.InklingRelDecode.Proof.Common.PendStep
public import Kernels.InklingRelDecode.Proof.Common.WarpStep
public import Kernels.InklingRelDecode.Proof.Top.Prog.PollAt

@[expose] public section

/-! # A pending released lane steps, or its next event is a failed poll

The class of the lane's next instruction decides: the library's steps for the ordinary kinds, the
register request, the allocation and the Tensor Memory stores (`pend_step`), the read at an input
address (`Prog.read_step`); a poll is `Prog.poll_pend`, a warp collective `warp_steps`, which
needs the facts of the pairs of lanes of each warp. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem Prog.step_pend_gen (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hm : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g)
    (hpairs : ∀ {g h : Nat}, SameWarp L g h →
      Sched.WarpPair m (schedule Q L) X (CollAt Q L) (collS Q L) g h) :
    Sched.Steps (schedule Q L) m X (.thread g) ∨ ∃ pc, FailsAt L m X g pc :=
  pend_step (Prog.nextEnv hp hs hm hf) hpd hrel hp hf
    (fun hne hrun hl hout => Prog.read_step hp hs hm hf hpd hne hrel hrun hl hout)
    (fun h hk => Prog.poll_pend hp hs hm hf hpd hrel h hk)
    (fun hσ hat => warp_steps hp hs (Prog.nextEnv hp hs hm hf) hf hpairs hpd hrel hσ hat)

end PTX.Kernels.InklingRelDecode.Proof.Top
