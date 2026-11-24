-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Async
public import Kernels.FlashAttn4Fwd.Proof.Progress.NextSteps
public import Kernels.FlashAttn4Fwd.Proof.Progress.Collective
public import Kernels.FlashAttn4Fwd.Proof.Progress.PollWaits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls
public import Kernels.FlashAttn4Fwd.Proof.Progress.WarpColl

@[expose] public section

/-! # The progress assembly (draft): every open obligation steps

Every open obligation of a maximal execution steps (`obl_steps`), so every maximal execution is
complete (`progress_of_remaining`, through `Descent.progress_of_steps` and the cover).

A pending thread splits on its last event.

* Released, without a state: the thread performs its undefined behaviour
  (`Descent.dead_steps`); a stopped machine (`some none`) is excluded by the machine's tracking
  of every thread (`htr`, `tracked` of the thread layer).
* Released, at a state: the kind of its next event (`nextKind`) picks the class. A plain
  event, a read, the exit, an mbarrier initialization or arrival, a copy or store issue, an MMA,
  a commit, a cluster barrier operation, a named-barrier arrival, a register request, a paired
  Tensor Memory operation, a Tensor Memory load or store or their waits and a bulk-group wait
  are performed (`next_steps`, from the thread layer's `NextFacts` and the facts of the whole
  execution `NextSafe`, which the root proves from the safety goal). At an mbarrier poll the
  thread is at a wait whose blockers are earlier (`polls_of`, from `PollsBlocked`, which
  `Polls/Waits.lean` proves from `Remaining.polls`, `Remaining.pollInputs` and the protocols'
  blocker exports), which steps by `Sched.mbar_at_steps`. At a warp collective the whole warp
  performs it, or a lane of the warp is earlier (`warp_next_steps`, from the thread layer's
  `WarpCollFacts`).
* Blocked (`Sched.thread_cases`): at an unrecorded cluster-barrier operation, a register request, a
  paired Tensor Memory operation, a named-barrier generation, a warp-collective `tcgen05` event
  or an unrecorded `bar.arrive`, it steps by its class (`blocked_steps`,
  `Progress/Collective.lean`), from the facts of `Remaining.waits`.

The asynchronous obligations: a commit's delivery steps (`commit_steps`); CLC requests are
always notified in a maximal execution (`clc_steps`); bulk copies are not issued
(`bulk_steps`); tensor copies and tensor stores complete once their sources are fixed
(`tensor_steps`, `store_steps`, with the protocols' `AsyncSources`); the paired Tensor Memory
requests drain or pass to a pending lane (`tmem_steps`); MMAs complete once their operands have
sources (`mma_steps`).

`Remaining` holds the facts the layer below and the classes not written yet must supply; each
field names the classes it stands for. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX Classical

noncomputable section

/-- The descent step of an obligation in a maximal execution. -/
abbrev StepsAt (L : Launch) (mem0 : Mem0) (X : Execution) (o : Descent.Obligation) : Prop :=
  Sched.Steps (timed L) mem0 X o

/-- **The remaining premises of the progress goal.** -/
structure Remaining (L : Launch) (mem0 : Mem0) : Prop where
  /-- Every commit has mask 3 over a cluster of two (`TcFacts.commit_spec`), so all commits
  target the same ranks: a commit's arrive-ons can be performed in issue order. -/
  commit_mask : ∀ X, Consistent L kernel asms mem0 X → ∀ (i : EvId) (sp : TcCommit.Spec),
    X.Commit i sp → sp.mask = 3 ∧ sp.clusterSize = 2
  /-- The thread layer's facts of a thread's next event (`next_steps`), for every consistent
  execution. -/
  next : ∀ X, Consistent L kernel asms mem0 X → NextFacts L X
  /-- The thread layer's facts at the mbarrier polls (`ProgressPolls`: per wait class, the
  waiter polls its object and a producer short of the waiter's phase lags it), for every
  consistent execution. -/
  polls : ∀ X, Consistent L kernel asms mem0 X → ProgressPolls L X
  /-- The thread layer's existing exports the poll blockers read (`PollInputs`: the routes'
  facts and the older facts), for every consistent execution of a launch satisfying the
  precondition. -/
  pollInputs : ∀ P X, Pre P L mem0 → Consistent L kernel asms mem0 X → PollInputs P L X
  /-- The thread layer's facts at the warp collectives (`WarpCollFacts`: the lanes of a warp
  agree on their warp collectives by ordinal, release before them alike, exit after all of them,
  and a lane not yet at a collective is earlier), for every consistent execution. -/
  warpColl : ∀ X, Consistent L kernel asms mem0 X → WarpCollFacts L X
  /-- The facts the collective waits use (`blocked_steps`), for every consistent execution: the
  thread layer's `ClusterFacts`, `TmemFacts`, `StatsFacts`, `TmemLifeFacts` and
  `ProgressWaitFacts`, and the register premises `RegMatch`, `RegExit` (from
  `Safety.RegFacts`, `regMatch_of`, `regExit_of`). -/
  waits : ∀ X, Consistent L kernel asms mem0 X → WaitInputs L X
  /-- The thread layer's exports the asynchronous obligations use (bulk copies, MMAs, tensor
  copies, tensor stores, the paired Tensor Memory requests), for every consistent execution of a
  launch satisfying the precondition. -/
  async : ∀ P X, Pre P L mem0 → Consistent L kernel asms mem0 X → AsyncInputs P L X

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A safe execution has no undefined behaviour. -/
theorem noUb_of_safe (hsafe : ¬ Unsafe L kernel asms mem0 X) : ¬ HasUb X :=
  fun h => hsafe (by unfold Unsafe; exact .inl h)

/-- A thread's earlier commit targets every rank a later one targets (`Remaining.commit_mask`). -/
theorem commit_prev (hR : Remaining L mem0) (hX : Consistent L kernel asms mem0 X) :
    ∀ (g j j' pc pc' : Nat) (sp sp' : TcCommit.Spec) (rank : Fin 16) (m : Loc),
      X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ → (fun _ => true : Nat → Bool) pc = true →
      X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ → j < j' →
      TcCommit.target sp' rank = some m → ∃ m', TcCommit.target sp rank = some m' := by
  intro g j j' pc pc' sp sp' rank m he _ he' _ ht
  obtain ⟨h1, h2⟩ := hR.commit_mask X hX _ sp ⟨pc, he⟩
  obtain ⟨h1', h2'⟩ := hR.commit_mask X hX _ sp' ⟨pc', he'⟩
  unfold TcCommit.target at ht ⊢
  rw [h1', h2'] at ht
  rw [h1, h2]
  split_ifs at ht with hc
  exact ⟨_, ite_eq_left_of_eq_true _ _ (eq_true hc)⟩

/-- **A commit's delivery steps**: when every MMA it tracks has started, the delivery happened
in a maximal execution, the commits of a thread delivering in issue order (as the commit-order
assumption's constraint asks); otherwise a tracked MMA is an open MMA obligation of smaller
rank. -/
theorem commit_steps (hR : Remaining L mem0) (hmax : Maximal L kernel asms mem0 X)
    (ho : Descent.Obl L X .commit) : StepsAt L mem0 X .commit := by
  by_cases hs : ∀ i, (∃ c, AsyncCopy.TracksMma X i c) → X.async.mmaStarted i = true
  · refine (ho fun i s rank m hi ht => ?_).elim
    exact Maximal.commit_notified_inOrder asms_wfStep hmax (commit_prev hR hmax.1) hi ht
      fun x hx => hs x ⟨i, hx⟩
  · push Not at hs
    obtain ⟨x, ⟨c, hx⟩, hns⟩ := hs
    obtain ⟨-, -, hta, -⟩ := hx
    refine .inr ⟨X, .mma, hmax, fun hall => ?_, by simp [Sched.rank]⟩
    have hd := hall x hta
    have := hmax.1.tma.2.1.2 x hd
    rw [this] at hns
    exact hns rfl

/-- A maximal execution has notified every target of every CLC request. -/
theorem clc_steps (hmax : Maximal L kernel asms mem0 X) (ho : Descent.Obl L X .clc) :
    StepsAt L mem0 X .clc :=
  (ho fun _ _ _ hi => Maximal.clc_notified_inOrder asms_wfStep hmax hi).elim

/-- The facts the classes of a released pending thread use, in a maximal execution. -/
theorem nextCtx (hR : Remaining L mem0) (hA : AsyncSources L mem0)
    (hN : ∀ X, Consistent L kernel asms mem0 X → NextSafe L X) (hpre : Pre P L mem0)
    (hs : SafeGoal kernel asms L mem0) (hmax : Maximal L kernel asms mem0 X) :
    NextCtx L mem0 X := by
  have hi := hR.async P X hpre hmax.1
  have hsafe := hs.2 X hmax.1
  exact ⟨hmax, hsafe, hR.next X hmax.1, hN X hmax.1,
    syncGuarded hmax.1 hsafe hi.rings hi.progress hi.tmem,
    fun _ _ _ _ he => hi.progress.no_release he,
    fun _ _ _ _ _ he => (hi.tmem.no_rmw he).elim, no_threadFence hmax.1, (hA.mma X hmax).2.2⟩

variable (hR : Remaining L mem0) (hA : AsyncSources L mem0)
    (hN : ∀ X, Consistent L kernel asms mem0 X → NextSafe L X) (hP : PollsBlocked L mem0)
    (htr : ∀ X, Consistent L kernel asms mem0 X → Frame.Tracked (code L) X) (hpre : Pre P L mem0)
include hR hA hN hP htr hpre

/-- **A pending thread steps.** -/
theorem thread_steps (hs : SafeGoal kernel asms L mem0) (hmax : Maximal L kernel asms mem0 X)
    {g : Nat} (hp : Frame.Pending L X g) : StepsAt L mem0 X (.thread g) := by
  have hX := hmax.1
  have hub := noUb_of_safe (hs.2 X hX)
  have hsound : ∀ g < L.threads, (code L g).Sound := (prologueFacts hpre hX).sound
  by_cases hrel : Step.Released L X g
  · cases hσ : Frame.stateAt (code L) X g (X.tr g).length with
    | none => exact Descent.dead_steps_inOrder asms_wfStep hmax hub hsound hp hσ hrel
    | some σ =>
      cases σ with
      | none => exact absurd hσ (htr X hX g _ hp.1)
      | some d =>
        cases hk : nextKind d with
        | wait =>
          obtain ⟨b, h, hb, h2⟩ := polls_of hP hmax hp hrel hσ hk
          have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
          exact Sched.mbar_at_steps asms_wfStep hub hmax hp hrel hne h hb h2
        | warp =>
          exact warp_next_steps hpre hs (htr X hX) (hR.next X hX) (hR.warpColl X hX) hmax
            hp hσ hk hrel
        | _ => exact next_steps (nextCtx hR hA hN hpre hs hmax) hp hσ hrel (by rw [hk]; exact id)
  · exact blocked_steps hpre hs htr hR.waits (nextCtx hR hA hN hpre hs hmax) hp hrel

/-- **Every open obligation steps.** -/
theorem obl_steps (hs : SafeGoal kernel asms L mem0) (hmax : Maximal L kernel asms mem0 X)
    {o : Descent.Obligation} (ho : Descent.Obl L X o) : StepsAt L mem0 X o := by
  have hi := hR.async P X hpre hmax.1
  have hsafe := hs.2 X hmax.1
  cases o with
  | thread g => exact thread_steps hR hA hN hP htr hpre hs hmax ho
  | bulk => exact bulk_steps hi.tmem ho
  | arriveOn => exact arriveOn_steps hi.tmem ho
  | mma =>
    obtain ⟨hos, hap, hinj⟩ := hA.mma X hmax
    exact mma_steps hmax (syncGuarded hmax.1 hsafe hi.rings hi.progress hi.tmem) hos hap hinj
      hi.score ho
  | clc => exact clc_steps hmax ho
  | tensor => exact tensor_steps hmax (hA.tensor X hmax) ho
  | store =>
    exact store_steps hmax (syncGuarded hmax.1 hsafe hi.rings hi.progress hi.tmem) (hA.store X hmax)
      ho
  | commit => exact commit_steps hR hmax ho
  | tmem => exact tmem_steps hpre hsafe hi.tmem hmax ho

/-- **Progress from the remaining premises**, given the sources of the asynchronous operations
(`AsyncSources`, from the protocols), the facts of the whole execution at a thread's next event
(`NextSafe`, from the safety goal) and the poll blockers (`PollsBlocked`, from
`Polls/Waits.lean`). -/
theorem progress_of_remaining (hs : SafeGoal kernel asms L mem0)
    : ProgressGoal kernel asms L mem0 :=
  Descent.progress_of_steps (Descent.Obl L) (Sched.rank (timed L)) (fun _ _ hc => Descent.cover hc)
    fun _ _ hmax ho => obl_steps hR hA hN hP htr hpre hs hmax ho

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
