-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Polls
public import Lemmas.Step.CtaBarFinishExit
public import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
public import Lemmas.Flow.NotClc

@[expose] public section

/-!
# The blocking last events of a pending thread

A pending thread whose last event is not released (`Step.Released` fails) has one blocking part
(`Sched.thread_cases`). The kernel has no cluster barrier, no `bar.arrive`, no bulk-group wait and
no `cp.async` wait, so that part is a register request, a paired Tensor Memory operation that
cannot return yet (`Sched.TmemOpen`), an allocation that waits only for its warp's address store
(`Sched.PublishWait`), a named-barrier `bar.sync` or a warp-collective `tcgen05` event
(`thread_cases`). Each steps by its class: a register request that not every lane of its warp has
matched (`reg_steps`) and a warp-collective `tcgen05` event some lane of its warp has not reached
(`Sched.tc_steps`) wait for a lane of their warp that is pending and earlier; a named barrier and
a paired Tensor Memory operation are classes of `Remaining` (`bar`, `tmem`); a nonleader lane's
allocation waits for lane 0 to make the address store (`Alloc.lean`: `publish_steps`). A thread of
the launch is not canceled (`no_canceled`): the kernel issues no cancellation request.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel has no bulk-group wait. -/
theorem kernel_noBulkWait : kernel.code.all (fun ins => !bulkWaitOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no bulk-group wait.** -/
theorem no_bulkWait (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {md : BulkGroup.WaitMode} {n : Nat},
      X.get i ≠ some ⟨pc, .bulkWait md n⟩ :=
  fun he => no_kind_of_code hX bulkWaitOp (fun k => ∃ md n, k = .bulkWait md n)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_bulkWait_op hf hk)
    kernel_noBulkWait he ⟨_, _, rfl⟩

/-- **The blocking part of a thread's last event** (`Sched.thread_cases`). The kernel has no
cluster barrier, no `bar.arrive`, no bulk-group wait and no `cp.async` wait, and a paired Tensor
Memory operation that cannot return cannot return yet or waits for its warp's address store
(`Sched.tmemWait_cases`). -/
theorem thread_cases (hX : Consistent L kernel asms mem0 X) {g : Nat} (hg : g < L.threads)
    (h : ¬ Step.Released L X g) :
    Sched.RegWait L X g ∨ Sched.TmemOpen L X g ∨ Sched.PublishWait L X g ∨ Sched.BarWait L X g ∨
      Sched.TcWait L X g := by
  rcases Sched.thread_cases hX hg (fun _ _ => no_asyncWait hX) h with
    ⟨pc, op, hq, -⟩ | hw | hw | hw | hw | ⟨pc, id, cnt, hq, -⟩ | ⟨pc, md, n, hq, -⟩
  · exact (Safety.no_cluster hX hq).elim
  · exact .inl hw
  · rcases Sched.tmemWait_cases hX hw with hw | hw
    · exact .inr (.inl hw)
    · exact .inr (.inr (.inl hw))
  · exact .inr (.inr (.inr (.inl hw)))
  · exact .inr (.inr (.inr (.inr hw)))
  · exact (Consistent.noBarArrive Safety.kernel_noBarArrive hX (g, _) pc id cnt hq).elim
  · exact (no_bulkWait hX hq).elim

/-! ### Register requests -/

/-- **The facts of the register requests of a launch.** A thread makes several requests (`inc 256`,
`dec 24`); the requests of the lanes of a warp are matched by ordinal. A lane of the warp of a
thread blocked at its request of ordinal `k` that has made no request of that ordinal is pending
and earlier: a lane exits only after the requests of its warp's lanes (`exit`), and a lane that has
made none of ordinal `k` is no later than the blocked thread's state before it (`before`), which
the state after the request exceeds (`after`). -/
structure RegWaitFacts (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (X : Execution) : Prop where
  /-- A lane exits only after every request of a lane of its warp: if some lane of its warp made a
  request of ordinal `k`, so did it (`Safety.Protocol.regAligned`, the lanes of a warp run their
  `setmaxnreg` in lockstep and no lane exits early). -/
  exit : ∀ {e : EvId} {pc n inst : Nat} {inc : Bool}, SetMaxNReg.Request X e pc inc n inst →
    ∀ {h j pc' : Nat}, SameWarp L e.1 h → X.get (h, j) = some ⟨pc', .exit⟩ →
      ∃ j' pc'' inc' n' inst', SetMaxNReg.Request X (h, j') pc'' inc' n' inst' ∧
        SetMaxNReg.ordinal X (h, j') = SetMaxNReg.ordinal X e
  /-- A lane `h` of the warp of `g` that has made no register request of the ordinal of `g`'s
  request at `k` is, at its current time, no later than `g`'s state before that request. (Only the
  lanes of the warp, not every thread of the launch: no time function makes the statement true of a
  default-partition thread at the end of its machine, which has made three requests and none of
  ordinal three, against a worker's fourth request, which is the head of the dispatch loop in its
  later round and is before the barrier the default thread has passed; the development notes.) -/
  before : ∀ {g h k pc n inst : Nat} {inc : Bool} {d : TSt}, g < L.threads → h < L.threads →
    SameWarp L g h →
    (∀ j pc' inc' n' inst', SetMaxNReg.Request X (h, j) pc' inc' n' inst' →
      SetMaxNReg.ordinal X (h, j) ≠ SetMaxNReg.ordinal X (g, k)) →
    X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ → St Q L X g k = some (some d) →
    Sched.threadTime (timed T Q L) X h ≤ T g d
  /-- After a register request the thread is at a state later than the one before it, or its
  machine has stopped. -/
  after : ∀ {g k pc n inst : Nat} {inc : Bool} {d : TSt}, g < L.threads →
    X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ → St Q L X g k = some (some d) →
    (∃ d', St Q L X g (k + 1) = some (some d') ∧ T g d < T g d') ∨ St Q L X g (k + 1) = none

/-- A thread of the warp of `g` in a given lane. -/
theorem warp_mate (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) {lane : Nat}
    (hl : lane < 32) : ∃ h, h < L.threads ∧ SameWarp L g h ∧ laneOf L h = lane := by
  have hb := hpre.block
  refine ⟨g / L.block * L.block + g % L.block / 32 * 32 + lane, ?_, ?_, ?_⟩
  all_goals simp only [Launch.threads, SameWarp, SameCta, laneOf, hb] at hg ⊢
  · omega
  · refine ⟨⟨hg, ?_, ?_⟩, ?_⟩ <;> omega
  · omega

/-- A thread with no exit event is pending, when it is launched: the kernel issues no cancellation
request. -/
theorem pending_of_noExit (hX : Consistent L kernel asms mem0 X) {h : Nat} (hh : h < L.threads)
    (hnx : ∀ j pc, X.get (h, j) ≠ some ⟨pc, .exit⟩) : Frame.Pending L X h :=
  ⟨hh, no_canceled hX _ hh, fun pc hl => hnx _ pc (by
    change (X.tr h)[(X.tr h).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hl)⟩

/-- **Progress at a register request.** A pending thread whose last event is a register request
that not every lane of its warp has matched steps: a lane with no request is pending and earlier.
(In a safe execution some lane of the warp has no matching request,
`Step.missing_member_lane`. Two requests of lanes of one warp match, so that lane has made no
request at all, and so it has not exited: it is pending. It is at a state no later than the
requests' time, while the blocked thread is after it, so the lane ranks below the blocked
thread.) -/
theorem reg_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hw : RegWaitFacts T Q L X) (hmax : Maximal L kernel asms mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (hrw : Sched.RegWait L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  obtain ⟨pc, inc, n, inst, hreq, hm⟩ := hrw
  have hX := hmax.1
  have hg := hp.1
  have hsafe := hs.2 X hX
  have hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ := hreq
  have hlen : 0 < (X.tr g).length := by
    have : (X.tr g).length - 1 < (X.tr g).length := len_of_get hlast
    omega
  obtain ⟨lane, hl, hmiss⟩ := Step.missing_member_lane hsafe hreq hm
  obtain ⟨h, hh, hwh, hlane⟩ := warp_mate hpre hg hl
  obtain ⟨-, hno⟩ := hmiss h hh hwh hlane
  have hnx : ∀ j pc', X.get (h, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    obtain ⟨j', pc'', inc', n', inst', hr', hord⟩ := hw.exit hreq hwh hj
    exact hno j' pc'' inc' n' inst' hr' hord
  have hph := pending_of_noExit hX hh hnx
  refine Sched.earlier_steps hmax hrel hph ?_
  obtain ⟨dg, hσg⟩ : ∃ dg, St Q L X g ((X.tr g).length - 1) = some (some dg) :=
    Frame.state_of_noUb (C := code L Q) hS hX htr (Sched.safe_noUb hsafe) hlast
  have h1 := hw.before hg hh hwh hno hlast hσg
  rcases hw.after hg hlast hσg with ⟨d', hd', hlt⟩ | hnone
  · rw [Nat.sub_add_cancel hlen] at hd'
    rw [threadTime_eq hd']
    omega
  · rw [Nat.sub_add_cancel hlen] at hnone
    rw [threadTime_stop hσg hnone]
    omega

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
