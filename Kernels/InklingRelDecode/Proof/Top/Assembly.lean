-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Followed
public import Kernels.InklingRelDecode.Proof.Top.Prog.KvEmpty
public import Kernels.InklingRelDecode.Proof.Top.Prog.KvReady
public import Kernels.InklingRelDecode.Proof.Top.Prog.DataPoll
public import Kernels.InklingRelDecode.Proof.Top.Prog.PReady
public import Kernels.InklingRelDecode.Proof.Top.Prog.OFinal
public import Kernels.InklingRelDecode.Proof.Top.Prog.Other
public import Kernels.InklingRelDecode.Proof.Top.Prog.Blocked
public import Kernels.InklingRelDecode.Proof.Top.Prog.Tmem
public import Kernels.InklingRelDecode.Proof.Top.Prog.Tensor
public import Kernels.InklingRelDecode.Proof.Top.Prog.Commit
public import Kernels.InklingRelDecode.Proof.Top.Prog.Tc
public import Lemmas.Kernel.Descent
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll
import Kernels.InklingRelDecode.Proof.Top.Prog.ReadStep
import Kernels.InklingRelDecode.Proof.Top.Prog.StepAt
import Kernels.InklingRelDecode.Proof.Top.Prog.WarpRel
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

private theorem poll_steps (hp : Pre Q L m)
    (hs : SafeGoal kernel Assumptions.all L m) {X} (hm : Maximal L kernel Assumptions.all m X)
    (hf : Follow Q L X) {g pc} (hg : Frame.Pending L X g) (hr : Step.Released L X g)
    (failed : FailsAt L m X g pc) : Sched.Steps (schedule Q L) m X (.thread g) := by
  obtain ⟨_,_,_,Y,hY,_,he⟩ := id failed
  have sites := (Lib.poll_site hY he).1
  simp only [Lib.pollSites,List.mem_cons,List.not_mem_nil,or_false] at sites
  rcases sites with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Prog.score hp (fun _ hY => followed hp hY) hs hm hf hg hr failed
  · exact Prog.done hp (fun _ hY => followed hp hY) hs hm hf hg hr failed
  · exact Prog.kvEmpty hp (fun _ hY => followed hp hY) hs X hm hf hg hr failed
  · exact Prog.kvReady hp (fun _ hY => followed hp hY) hs X hm hf hg hr failed
  · exact Prog.pReady hp (fun _ hY => followed hp hY) hs X hm hf hg hr failed
  · exact Prog.oFinal hp (fun _ hY => followed hp hY) hs X hm hf hg hr failed

theorem progress (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m) :
    ProgressGoal kernel Assumptions.all L m := by
  apply Descent.progress_of_steps (Descent.Obl L) (Sched.rank (schedule Q L))
    (fun _ _ hc => Descent.cover hc)
  intro X o hm hob
  have hX := hm.1
  have hf := followed hp hX
  have hu := Sched.safe_noUb (hs.2 X hX)
  have hpairs : ∀ {g h : Nat}, SameWarp L g h →
      Sched.WarpPair m (schedule Q L) X (CollAt Q L) (collS Q L) g h := fun hsw =>
    Export.warp_pairs hp hX hf (fun h => Protocol.Shared.role_bytes hp hX h)
      (fun y => .of_noUb hu y) (fun _ => Prog.warp_rel hp hs hm hf)
      (fun _ => Prog.warp_dead hp hs hm hf) hsw
  cases o with
  | thread g =>
    by_cases hr : Step.Released L X g
    · obtain step | ⟨pc,fail⟩ := Prog.step_pend_gen hp hs hm hf hob hr hpairs
      · exact step
      · exact poll_steps hp hs hm hf hob hr fail
    · exact Prog.named hp hs X hm hf hob hr (Prog.blocked_kind hp hm.1 hob hr)
  | tensor =>
    exact Prog.tensor hp hm (hs.2 X hm.1) (Protocol.Shared.tensor_input_bytes hp hm.1 hf) hob
  | commit => exact Prog.commit hp hm hf hob
  | mma => exact Prog.mma hp hs X hm hf _ (by simp) hob
  | tmem => exact Prog.tmem hp hs X hm hf _ (by simp) hob
  | bulk | arriveOn | clc | store => exact Prog.other hs X hm hf _ (by simp) hob

end PTX.Kernels.InklingRelDecode.Proof.Top
