-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Remaining
public import Kernels.InklingRelDecode.Proof.Progress.Words

@[expose] public section

/-!
# `progress_goal`: every open obligation of a maximal execution steps

`ProgressGoal` is `∀ X, Maximal L K A mem0 X → Complete L X` (`Lemmas/Kernel/Goals.lean`): every
maximal execution is complete. The proof is the library's descent (`Descent.progress_of_steps`):
every incomplete maximal execution has an open obligation (`Descent.cover`), and every open
obligation of a maximal execution steps (`obl_steps`): the execution has a counted consistent
extension, or an open obligation of strictly smaller rank in a maximal execution
(`Descent.Steps`). Ranks are the pending threads' (twice the virtual time of their machine state,
`Rank.lean`) and the asynchronous obligations' (below every thread at a wait).

A pending thread splits on its last event.

* **Released, its machine stopped** (the state is `none`): the thread performs its undefined
  behaviour (`Descent.dead_steps_inOrder`); a state the machine does not follow (`some none`) is
  excluded by the machines' tracking of every thread (`ThreadFacts.tracked`).
* **Released, at a state**: the kind of its next event (`nextKind`) picks the class. A plain event,
  a read, the exit, an mbarrier initialization or arrival, a tensor copy, an MMA, a commit, a
  named-barrier arrival, a Tensor Memory load or store or their waits, a paired Tensor Memory
  operation are performed (`next_steps`, from `NextFacts` and `NextSafe`); at a register request it
  steps by `Remaining.regIssue`; at an mbarrier poll the thread is at a wait whose blockers are
  earlier (`polls_of`, from `Remaining.polls`), which steps by `Sched.mbar_at_steps`; at a warp
  collective the whole warp performs it, or a lane of the warp is earlier (`warp_next_steps`, from
  `Remaining.warpColl`).
* **Blocked** (`thread_cases`): at an unreleased register request, named barrier, paired Tensor
  Memory operation or warp-collective `tcgen05` event it steps by its class (`blocked_steps`); at
  an allocation that waits only for its warp's address store, lane 0 makes the store or has made
  it (`publish_steps`).

The asynchronous obligations: a commit's delivery steps (`commit_steps`); the kernel issues no
bulk copy, `cp.async.mbarrier.arrive`, tensor store or CLC request; tensor copies complete once
their sources are fixed (`tensor_steps`); MMAs complete once their operands have sources
(`mma_steps`); the paired Tensor Memory requests drain (`Remaining.tmemSteps`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at a state steps**, by the kind of its next event. -/
theorem next_steps {T : Nat → TSt → Nat} (hc : NextCtx Q L mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) {s : TSt} (hσ : St Q L X g (X.tr g).length = some (some s))
    (hrel : Step.Released L X g)
    (hr : nextKind s ≠ .wait ∧ nextKind s ≠ .warp ∧ nextKind s ≠ .reg) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  cases hk : nextKind s with
  | wait | warp | reg => rw [hk] at hr; simp at hr
  | bar => exact bar_next_steps hc hp hσ hk hrel
  | tmem => exact tmem_next_steps hc hp hσ hk hrel
  | init => exact init_next_steps hc hp hσ hk hrel
  | arrive => exact arrive_next_steps hc hp hσ hk hrel
  | tensorLoad => exact tensorLoad_next_steps hc hp hσ hk hrel
  | mma => exact mma_next_steps hc hp hσ hk hrel
  | commit => exact commit_next_steps hc hp hσ hk hrel
  | tcLoad => exact tcLoad_next_steps hc hp hσ hk hrel
  | tcStore => exact tcStore_next_steps hc hp hσ hk hrel
  | read => exact read_next_steps hc hp hσ hk hrel
  | quiet => exact quiet_next_steps hc hp hσ hk hrel
  | store => exact store_next_steps hc hp hσ hk hrel
  | allocStore => exact allocStore_next_steps hc hp hσ hk hrel
  | exit => exact exit_next_steps hc hp hσ hk hrel
  | other =>
    -- the template of a state of no kind is undefined behaviour
    obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
    rw [hk] at hm
    rcases hm with ⟨f, rfl⟩ | hm
    · exact ub_steps hc hp hrel hrun hl hout
    · exact hm.elim

/-- **A pending thread whose last event blocks steps**, by the class of its blocking part. -/
theorem blocked_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hR : Remaining Q L mem0) (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (htr : ∀ Y, Consistent L kernel asms mem0 Y → Frame.Tracked (code L Q) Y)
    (hmax : Maximal L kernel asms mem0 X) (hc : NextCtx Q L mem0 X) (hf : ThreadFacts Q L mem0 X)
    {g : Nat} (hp : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) : Sched.Steps (timed hR.time Q L) mem0 X (.thread g) := by
  have hX := hmax.1
  rcases thread_cases hX hp.1 hrel with hw | hw | hw | hw | hw
  · exact reg_steps hpre hs hS (htr X hX) (hR.regWaits X hX) hmax hp hrel hw
  · exact hR.tmemSteps.1 X g hmax hp hrel hw
  · obtain ⟨pc, grp, dst, n, hlast, hrr, hMissing⟩ := hw
    exact publish_steps hpre hc hf hlast hrr hMissing
  · exact hR.barSteps X g hmax hp hrel hw
  · exact Sched.tc_steps (hs.2 X hX) hS (htr X hX) (hR.tcWaits X hX) hmax hp hrel hw

variable (hpre : Pre Q L mem0) (hso : SmOb Q L mem0)
  (hP : ∀ X, Consistent L kernel asms mem0 X → Premises Q L X)
  (hs : SafeGoal kernel asms L mem0) (hR : Remaining Q L mem0)

include hpre hso hP hs hR in
/-- **A pending thread steps.** -/
theorem thread_steps (hmax : Maximal L kernel asms mem0 X) {g : Nat} (hp : Frame.Pending L X g) :
    Sched.Steps (timed hR.time Q L) mem0 X (.thread g) := by
  have hX := hmax.1
  have hf := threadFacts hpre hso hX (hP X hX)
  have hsafe := hs.2 X hX
  have hub := Sched.safe_noUb hsafe
  have hc : NextCtx Q L mem0 X := ⟨hmax, hsafe, hf.sound, alloc_next hX hf,
    ⟨hR.reads X hX, words hpre hX hf, alloc_base hX hsafe⟩, syncGuarded hX hsafe,
    (hR.async.mma X hmax).2.2, hR.fresh X hX⟩
  by_cases hrel : Step.Released L X g
  · cases hσ : St Q L X g (X.tr g).length with
    | none => exact Descent.dead_steps_inOrder asms_wfStep hmax hub hf.sound hp hσ hrel
    | some σ =>
      cases σ with
      | none => exact absurd hσ (hf.tracked g _ hp.1)
      | some d =>
        have hne : nextKind d = .wait → X.tr g ≠ [] := fun hk =>
          ne_nil_of_kind hσ (by rw [hk]; decide) (by rw [hk]; decide)
        by_cases hk : nextKind d = .wait
        · obtain ⟨b, h, hb, h2⟩ := polls_of hR.polls hmax hp hrel hσ hk (hR.wait_time g d hk)
          exact Sched.mbar_at_steps asms_wfStep hub hmax hp hrel (hne hk) h hb h2
        by_cases hk' : nextKind d = .warp
        · exact warp_next_steps hpre hs hf.sound hf.tracked (hR.warpColl X hmax) hmax hp hσ hk' hrel
            (allocStored_of hpre hX hf hp.1 hσ (by rw [hk']; decide))
        by_cases hk'' : nextKind d = .reg
        · exact hR.regIssue X g d hmax hp hσ hk'' hrel
        exact next_steps hc hp hσ hrel ⟨hk, hk', hk''⟩
  · exact blocked_steps hpre hs hR hf.sound
      (fun Y hY => (threadFacts hpre hso hY (hP Y hY)).tracked) hmax hc hf hp hrel

include hpre hso hP hs hR in
/-- **Every open obligation steps.** -/
theorem obl_steps (hmax : Maximal L kernel asms mem0 X) {o : Descent.Obligation}
    (ho : Descent.Obl L X o) : Sched.Steps (timed hR.time Q L) mem0 X o := by
  have hX := hmax.1
  have hf := threadFacts hpre hso hX (hP X hX)
  have hsafe := hs.2 X hX
  cases o with
  | thread g => exact thread_steps hpre hso hP hs hR hmax ho
  | bulk => exact bulk_steps hX ho
  | arriveOn => exact arriveOn_steps hX ho
  | mma =>
    obtain ⟨hos, hap, hinj⟩ := hR.async.mma X hmax
    exact mma_steps hmax (syncGuarded hX hsafe) hos hap hinj ho
  | clc => exact clc_steps hmax ho
  | tensor => exact tensor_steps hmax (hR.async.tensor X hmax) ho
  | store => exact store_steps hX ho
  | commit => exact commit_steps hpre hf hmax ho
  | tmem => exact hR.tmemSteps.2 X hmax ho

include hpre hso hP hs hR in
/-- **`ProgressGoal`: every maximal execution of the Inkling kernel is complete**, given `Pre`, the
softmax region's obligations, the thread machines' premises, the safety goal and the progress
layer's remaining facts (`Remaining`). -/
theorem progress_goal : ProgressGoal kernel Assumptions.all L mem0 :=
  Descent.progress_of_steps (Descent.Obl L) (Sched.rank (timed hR.time Q L))
    (fun _ _ hc => Descent.cover hc)
    fun _ _ hmax ho => obl_steps hpre hso hP hs hR hmax ho

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
