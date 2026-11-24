-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Remaining
public import Kernels.InklingRelDecode.Proof.Progress.Collective
public import Kernels.InklingRelDecode.Proof.Interface.PgBar

@[expose] public section

/-!
# A blocked `bar.sync 1` steps

Barrier 1 is `barrier.sync 1` of all eight warps without a thread count (`Bar.bar1_shape`,
`Bar.bar1_sources`), so a blocked `bar.sync 1` steps by the library's argument for a barrier of one
group (`Sched.bar_sync_steps`), given the `time` facts of its participant lanes: a lane that has
made at most the thread's ordinal of events on the barrier has not exited and is no later than the
thread's state before the event (`hlag`), and the thread's state after the event is later
(`hafter`, `Sched.threadTime_after`). Barrier 0 has three groups (`WfBarSteps.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A CTA barrier fault makes a consistent execution unsafe. -/
theorem fault_unsafe (hs : SafeGoal kernel asms L mem0) {Y : Execution}
    (hY : Consistent L kernel asms mem0 Y) : ¬ CtaBarFault L Y :=
  fun hf => hs.2 Y hY (by unfold Unsafe; simp [hf])

/-- **A blocked `bar.sync 1` steps**, given the `time` facts of its participant lanes. -/
theorem bar1_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) {g pc : Nat} (hp : Frame.Pending L X g)
    (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) 1 none pc) {d : TSt}
    (hd : St Q L X g ((X.tr g).length - 1) = some (some d))
    (hafter : (∃ d', St Q L X g ((X.tr g).length - 1 + 1) = some (some d') ∧ T g d < T g d') ∨
      St Q L X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block →
      (X.tr y).countP (Execution.isBarId 1) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 1) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hg := hp.1
  have hgt : T g d < Sched.threadTime (timed T Q L) X g :=
    Sched.threadTime_after (M := timed T Q L) hlen hd hafter
  refine Sched.bar_sync_steps asms_wfStep (fun Y hY => fault_unsafe hs hY) hmax hp hnr hlen hlast
    (Bar.bar1_shape hpre) (Bar.bar1_sources hpre hmax.1) fun y hy _ hle => ?_
  have hyt := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy
  have hdiv := (NamedBar.lane_cta (c := g / L.block) (NamedBar.block_pos_of_thread_lt hg) hy).1
  obtain ⟨hnx, hlt⟩ := hlag _ hyt hdiv hle
  exact ⟨hnx, by omega⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
