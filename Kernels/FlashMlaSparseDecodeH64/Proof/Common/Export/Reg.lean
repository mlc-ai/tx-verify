-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Lemmas.Kernel.Progress.RegW
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegReq

@[expose] public section

/-! # Progress at a register request

A pending lane blocked at a `setmaxnreg` that not every lane of its warp has made steps
(`reg_steps`, by `Sched.reg_stepsW`): the requests of one warp match (`reg_match`: every request is
its thread's first, at its warpgroup's pc and count), an `exit` follows a request (`reg_exit`),
and on the time table a lane without a request is no later than its warp's request time and a
lane after it is later (`Common/RegReq.lean`, the state taken privately). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Lanes of one warp have one warp index. -/
private theorem warp_same (hp : Pre P L m) {g h : Nat} (hw : SameWarp L g h) :
    warp L g = warp L h := by
  obtain ⟨-, hs⟩ := hw
  simp only [warp, tidOf_x_eq hp, ← hp.block]
  exact hs

/-- **The register requests of one warp match.** -/
theorem reg_match (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) : Sched.RegMatch L X := by
  intro e f pc pc' n n' inst inst' inc inc' _ _ hw he hf
  obtain ⟨g, k⟩ := e
  obtain ⟨h, j⟩ := f
  have hwe := warp_same hp hw
  obtain ⟨_, _, _, hpg⟩ := req_state hp hX hFw hnu he
  obtain ⟨_, _, _, hph⟩ := req_state hp hX hFw hnu hf
  simp only at hwe hpg hph
  have hpc : pc = pc' := by omega
  subst hpc
  obtain ⟨ins, hc, hop⟩ := req_op hX he
  obtain ⟨ins', hc', hop'⟩ := req_op hX hf
  rw [hc] at hc'
  cases hc'
  rw [hop] at hop'
  cases hop'
  refine ⟨hw, ?_, pc, inc, n, inst, inst', he, hf⟩
  show ((X.tr g).take k).countP SetMaxNReg.isRequest = ((X.tr h).take j).countP _
  rw [req_first hp hX hFw hnu he, req_first hp hX hFw hnu hf]

/-- **A thread exits after its register request.** -/
theorem reg_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) : Sched.RegExit L X :=
  fun _ he => req_exit hp hX hFw hnu he

/-- **A lane blocked at a register request steps.** -/
theorem reg_steps (hp : Pre P L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hFw : Follow P L X) {g : Nat}
    (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (hw : Sched.RegWait L X g) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hX := hmax.1
  have hnu := Sched.safe_noUb (hs.2 X hX)
  have hb : L.block % 32 = 0 := by rw [hp.block]
  refine Sched.reg_stepsW hs (reg_match hp hX hFw hnu) (reg_exit hp hX hFw hnu) hb (regT L)
    (fun {g h} hw => ?_) (fun hh hno => req_before hp hX hFw hnu hh hno)
    (fun {g k pc n inst inc} _ he => ?_) hmax hpd hrel hw
  · have hwe := warp_same hp hw
    simp only [warp, tidOf_x_eq hp] at hwe
    simp only [regT, wgOf, tidOf, tidOf_x_eq hp]
    have : g % 384 / 128 = h % 384 / 128 := by omega
    rw [this]
  · obtain ⟨σ, hσ, hlt⟩ := req_after hp hX hFw hnu he
    rw [timed_eq]
    exact ⟨σ, hσ, hlt⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
