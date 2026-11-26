-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Progress.Progress

@[expose] public section

/-!
# The progress dispatcher, with the release of a polling thread

`Proof/Progress/Progress.lean` asks, in its premise `pollState`, that the mbarrier a thread at
a poll state polls has a state, for every pending thread at such a state. For this kernel that
is false as stated: at its first visit of the poll of the state barrier (instruction 384) a
thread's last event is its third `bar.sync 0` (379), and as long as that barrier has not
released, the load leader may not have initialized the state barrier yet. The dispatcher only
uses the premise for a released thread, so `Premises2` adds `Step.Released L X g` to the
hypotheses of `pollState`; nothing else changes. `progress_of2` is `progress_of` over
`Premises2`. The text below was produced from `Progress.lean` by substitution; at the merge
of the two directories it replaces the structure `Premises` and the six theorems after it.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Step

noncomputable section

variable {L : Launch} {K : Kernel} {mem0 : Mem0} {A : List Assumption}

/-- **The premises of the progress skeleton** (`Premises` of `Proof/Progress/Progress.lean`
with the thread's release among the hypotheses of `pollState`), for a time table `M`, a
classification `cls` of
the machine states, the warp key `key` of a thread, the shape `pollEv` of the events a poll
state fires, and the participant warps `G id w` of the named barrier `id`. -/
structure Premises2 (M : Timed K A L) (mem0 : Mem0) (cls : ∀ g, (M.code g).D → Cls) {κ : Type}
    (key : Nat → κ) (pollEv : ∀ g, (M.code g).D → Event → Prop) (G : Nat → Nat → Prop) :
    Prop where
  -- Thread layer: the machines.
  /-- Every thread's site machine is sound. -/
  sound : ∀ g < L.threads, (M.code g).Sound
  /-- Every consistent execution is followed by the machines. -/
  tracked : ∀ X, Consistent L K A mem0 X → Frame.Tracked M.code X
  /-- A CTA is a whole number of warps. -/
  block32 : L.block % 32 = 0
  /-- The warp key is the same for the lanes of a warp. -/
  keyWarp : ∀ {g h : Nat}, SameWarp L g h → key g = key h
  /-- A thread at a free event or at a poll has made an event (the first event of every thread
  is a warp collective). -/
  started : ∀ X, Consistent L K A mem0 X → ∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) →
    cls g d = .free ∨ cls g d = .poll → X.tr g ≠ []
  -- Released thread at a free event (`read_stepsE` and its siblings, `Free.lean`).
  /-- The template a free state reaches is undefined behaviour or a free template. -/
  freeTmpl : ∀ X, Consistent L K A mem0 X → ∀ {g : Nat} {d : (M.code g).D} {t : TState}
    {m : Tmpl}, g < L.threads → Frame.stateAt M.code X g (X.tr g).length = some (some d) →
    cls g d = .free → (M.code g).AtD d t → (M.code g).inv d → out K A L g t = .ev m →
    (∃ f, m = .ub f) ∨ FreeTmpl m
  /-- An appended read whose bytes have sources keeps the assumptions' constraints. -/
  readWf : ∀ X, Maximal L K A mem0 X → ∀ g pc a bs r, (∀ e, NewRead L mem0 X g e r a bs) →
    ∀ a' ∈ A, a'.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r)
  /-- The conflicts at the bytes that are read are ordered (from data-race freedom). -/
  reads : ∀ X, Consistent L K A mem0 X → ReadsOrdered L X
  /-- Synchronization is guarded: successful polls are at canonical spin loops, no ordering
  comes from a release/acquire pair or a thread fence, no mbarrier record faults. -/
  guard : ∀ X, Consistent L K A mem0 X → SyncGuarded L K X
  /-- No store has release semantics. -/
  noRelease : ∀ X, Consistent L K A mem0 X → ∀ e pc a bs,
    X.get e = some ⟨pc, .wr a bs⟩ → a.release = false
  /-- No atomic has release semantics. -/
  noReleaseRmw : ∀ X, Consistent L K A mem0 X → ∀ e pc a o n,
    X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false
  /-- The kernel makes no thread fence. -/
  noFence : ∀ X, Consistent L K A mem0 X → ∀ e sem s, ¬ X.ThreadFence e sem s
  -- Released thread at a poll (`wait_site_stepsE`).
  /-- The instruction of a poll state is an acquiring `mbarrier.try_wait`. -/
  pollOp : ∀ {g : Nat} {d : (M.code g).D}, cls g d = .poll →
    ∀ ins, K.code[(M.code g).pc d]? = some ins → waitOp ins.op = true
  /-- The events a poll state fires have the state's shape. -/
  pollShape : ∀ {g : Nat} {d : (M.code g).D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState}, g < L.threads → cls g d = .poll → (M.code g).AtD d t →
    (M.code g).inv d → K.code[(M.code g).pc d]? = some ins →
    Fires ((M.code g).pc d) (eventTmpl A L g t ins.op) e o → pollEv g d e
  /-- The barrier a released thread at a poll state polls has a state (it was initialized).
  The thread's release matters at a poll that directly follows a barrier: only the release of
  that barrier shows that the thread that initializes the mbarrier has passed it. -/
  pollState : ∀ X, Maximal L K A mem0 X → ∀ {g : Nat} {d : (M.code g).D}, Frame.Pending L X g →
    Step.Released L X g →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → cls g d = .poll →
    ∀ l q ok sc, pollEv g d ⟨(M.code g).pc d, .wait l q ok true sc⟩ →
    ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before
  /-- When the polled barrier's phase has the poll's parity (the poll would fail), the thread
  has a blocker: an unfinished asynchronous operation, or a pending thread at an earlier time.
  The proof may use a consistent execution in which the failed poll is the thread's next
  event. -/
  pollBlk : ∀ X, Maximal L K A mem0 X → ∀ {g : Nat} {d : (M.code g).D}, Frame.Pending L X g →
    Step.Released L X g → Frame.stateAt M.code X g (X.tr g).length = some (some d) →
    cls g d = .poll → ∀ l q sc before,
    pollEv g d ⟨(M.code g).pc d, .wait l q false true sc⟩ →
    MBarrier.stateBefore (X.objects l) (X.objects l).length = some before →
    (∃ Y, Consistent L K A mem0 Y ∧ (Y.tr g).take (X.tr g).length = X.tr g ∧
      Y.get (g, (X.tr g).length) = some ⟨(M.code g).pc d, .wait l q false true sc⟩) →
    before.phase % 2 = q % 2 → Blk M X g
  /-- A poll state is at time 2 or later (the asynchronous obligations rank 0 and 1). -/
  pollTime : ∀ {g : Nat} {d : (M.code g).D}, cls g d = .poll → 2 ≤ M.time g d
  -- Released thread at a shuffle or an election (`warpColl_steps_lead`).
  coll : ∀ X, Maximal L K A mem0 X → CollLead mem0 M X key (fun g d => cls g d = .coll)
  -- Released thread at a warp matrix event (`Sched.matrix_steps`).
  matrix : ∀ X, Maximal L K A mem0 X → MatrixFacts M X key (fun g d => cls g d = .matrix)
  -- Thread blocked at a `bar.sync` (`barGroup_sync_stepsE`).
  /-- Every barrier event's barrier has a participant group: the warps `G id`. -/
  barGroup : ∀ X, Maximal L K A mem0 X → ∀ {g i pc id : Nat} {cnt : Option Nat} {m : BarMode},
    g < L.threads → X.get (g, i) = some ⟨pc, .bar id cnt m⟩ →
    ∃ p : Finset Nat, NamedBar.Shape L cnt p id ∧ NamedBar.Sources L X cnt p id ∧
      ∀ w ∈ p, G id w
  /-- After a barrier event the thread is at a later time, or its machine has stopped. -/
  barAfter : ∀ X, Maximal L K A mem0 X → ∀ {g j pc id : Nat} {cnt : Option Nat} {m : BarMode}
    {d : (M.code g).D}, g < L.threads → X.get (g, j) = some ⟨pc, .bar id cnt m⟩ →
    Frame.stateAt M.code X g j = some (some d) →
    (∃ d', Frame.stateAt M.code X g (j + 1) = some (some d') ∧ M.time g d < M.time g d') ∨
      Frame.stateAt M.code X g (j + 1) = none
  /-- A participant lane that has made no more events on the barrier than the thread had made
  before its arrival has not exited and is no later than the thread's state at the arrival. -/
  barLag : ∀ X, Maximal L K A mem0 X → ∀ {g y j pc id : Nat} {cnt : Option Nat}
    {d : (M.code g).D}, g < L.threads → y < L.threads → y / L.block = g / L.block →
    G id (y % L.block / 32) → X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩ →
    Frame.stateAt M.code X g j = some (some d) →
    (X.tr y).countP (Execution.isBarId id) ≤ ((X.tr g).take j).countP (Execution.isBarId id) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d
  -- The asynchronous operations (`tensor_stepsE`, `store_stepsE`).
  /-- Every tensor load is routed to its own CTA, has a valid non-empty descriptor, and reads
  global bytes that the launch defines and no operation of the execution writes. -/
  tensorSources : ∀ X, Maximal L K A mem0 X → TensorSources L mem0 X
  /-- Every tensor store is valid, is no reduction, and each shared byte it reads has a
  visible source write with a defined byte. -/
  storeSources : ∀ X, Maximal L K A mem0 X → StoreSources L X

variable {M : Timed K A L} {cls : ∀ g, (M.code g).D → Cls} {κ : Type} {key : Nat → κ}
  {pollEv : ∀ g, (M.code g).D → Event → Prop} {G : Nat → Nat → Prop} {lead : Nat}
  {X : Execution}

/-! ### The classes -/

section
variable (ha : AsmOk L K mem0 A lead) (hc : CodeOk L K mem0 A)
  (P : Premises2 M mem0 cls key pollEv G) (hs : SafeGoal K A L mem0)
include ha hc P hs

/-- **A released pending thread at a free event steps.** -/
theorem free_steps2 (hmax : Maximal L K A mem0 X) {g : Nat} (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hcls : cls g d = .free) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hub := safe_noUb (hs.2 X hX)
  have hne := P.started X hX hpd.1 hσ (.inl hcls)
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hpd
  obtain ⟨t1, ins, hl, hat, hinv, -, hout⟩ := Frame.end_at P.sound hpd.1 hrun hσ
  have henv : NextEnvE L K A mem0 X :=
    { max := hmax
      noUb := hub
      wf := ha.step
      readWf := P.readWf X hmax
      reads := P.reads X hX
      guard := P.guard X hX
      no_release := P.noRelease X hX
      no_release_rmw := P.noReleaseRmw X hX
      no_fence := P.noFence X hX }
  rcases P.freeTmpl X hX hpd.1 hσ hcls hat hinv hout with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_stepsE ha.step hX hpd.1 (.inl hne) hrel hrun hl hout
  · rcases hm with h | h | h | h | h | h | h | h | h | h
    · exact exit_stepsE henv hpd hne hrel hrun hl hout h
    · exact read_stepsE henv hpd hne hrel hrun hl hout h
    · exact store_stepsE henv hpd hne hrel hrun hl hout h
        fun _ _ _ _ he => (hc.no_kind hX rfl he).elim
    · exact quiet_stepsE henv hpd hne hrel hrun hl hout h
    · exact init_stepsE henv hpd hne hrel hrun hl hout h
    · exact arrive_stepsE henv hpd hne hrel hrun hl hout h
    · exact bulkWait_stepsE henv hpd hne hrel hrun hl hout h
    · exact tensorLoad_stepsE henv hpd hne hrel hrun hl hout h
    · exact tensorStore_stepsE henv hpd hne hrel hrun hl hout h
    · exact bar_stepsE henv hpd hne hrel hrun hl hout h

omit hc in
/-- **A released pending thread at a poll steps**: the poll succeeds, or the failed poll is
appended and a blocker ranks lower. -/
theorem poll_steps2 (hmax : Maximal L K A mem0 X) {g : Nat} (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hcls : cls g d = .poll) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hub := safe_noUb (hs.2 X hX)
  exact wait_site_stepsE ha.step hmax hub P.sound hpd hσ (P.started X hX hpd.1 hσ (.inr hcls))
    hrel (P.pollOp hcls) (P := pollEv g d)
    (fun hat hinv hi hf => P.pollShape hpd.1 hcls hat hinv hi hf)
    (fun l q ok sc hP => P.pollState X hmax hpd hrel hσ hcls l q ok sc hP)
    (fun l q sc before hP hst hY hpar =>
      P.pollBlk X hmax hpd hrel hσ hcls l q sc before hP hst hY hpar)
    (P.pollTime hcls)

/-- **A pending thread whose last event blocks steps**: it is at a `bar.sync` whose generation
is not done, or at a bulk-group wait that is not ready. -/
theorem blocked_steps2 (hmax : Maximal L K A mem0 X) {g : Nat} (hpd : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) : Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  rcases thread_cases hX hpd.1 (fun _ _ he => hc.no_kind hX rfl he) hrel with
    h | h | h | h | h | h | h
  · obtain ⟨pc, op, he, -⟩ := h
    exact (hc.no_kind hX rfl he).elim
  · obtain ⟨pc, inc, n, inst, he, -⟩ := h
    exact (hc.no_kind hX rfl he).elim
  · obtain ⟨pc, grp, dst, act, he, -⟩ := h
    exact (hc.no_kind hX rfl he).elim
  · exact barGroup_sync_stepsE ha.step.sameTr P.sound hs (P.barGroup X hmax) (P.barAfter X hmax)
      (P.barLag X hmax) (P.tracked X hX) hmax hpd hrel h
  · obtain ⟨k, -, ⟨⟨q, hq, hcq⟩, -⟩, -⟩ := h
    obtain ⟨pcq, kd, rfl⟩ := isTcColl_tc hcq
    exact (hc.no_kind hX rfl hq).elim
  · obtain ⟨pc, id, cnt, he, -⟩ := h
    exact (hc.no_kind hX rfl he).elim
  · -- a bulk-group wait waits for the tensor stores: the store obligation is open
    obtain ⟨pc, mode, n, hq, hr⟩ := h
    refine .inr ⟨X, .store, hmax, fun hd => hr ?_, rank_store_lt hrel⟩
    exact Step.BulkWait.ready_of_drained hX hq hd
      fun i s ⟨_, hi⟩ => (hc.no_kind hX (i := i) rfl hi).elim

/-- **A pending thread of a maximal execution steps.** -/
theorem thread_steps2 (hmax : Maximal L K A mem0 X) {g : Nat} (hpd : Frame.Pending L X g) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hub := safe_noUb (hs.2 X hX)
  have htr := P.tracked X hX
  by_cases hrel : Step.Released L X g
  swap
  · exact blocked_steps2 ha hc P hs hmax hpd hrel
  cases hσ : Frame.stateAt M.code X g (X.tr g).length with
  | none => exact dead_stepsE ha.step hmax hub P.sound hpd hσ hrel
  | some o =>
    cases o with
    | none => exact absurd hσ (htr g _ hpd.1)
    | some d =>
      have hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads →
          Step.Released L X h → Run K A L h {} (X.tr h) (some t) →
          Relation.ReflTransGen (Tau K A L h) t t1 → out K A L h t1 = .ev (.ub f) →
          ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
        fun hh hrl hrun hl hout => ub_ext ha hc hX hh hrl hrun hl hout
      cases hcls : cls g d with
      | free => exact free_steps2 ha hc P hs hmax hpd hrel hσ hcls
      | poll => exact poll_steps2 ha P hs hmax hpd hrel hσ hcls
      | coll =>
        exact warpColl_steps_lead hc.noVoteMode P.keyWarp P.sound hs htr (P.coll X hmax)
          P.block32 (hc.launched hX) (hc.notCanceled hX) ha.member (ha.det X hX)
          (ha.lanes X hX) hubx hmax hpd hσ hcls hrel
      | matrix =>
        exact matrix_steps P.keyWarp P.sound hs htr (P.matrix X hmax) P.block32
          (hc.launched hX) (hc.notCanceled hX)
          (fun g _ _ _ _ => ha.lanes X hX g _ fun x => quietFor_matrixBatch x) hubx hmax hpd hσ
          hcls hrel

omit hs in
/-- **An open asynchronous obligation of a maximal execution steps**: an unfinished tensor load
or tensor store; the kernel has no other asynchronous operation. -/
theorem async_steps2 (hmax : Maximal L K A mem0 X) {o : Descent.Obligation}
    (hth : ∀ g, o ≠ .thread g) (ho : Descent.Obl L X o) : Steps M mem0 X o := by
  have hX := hmax.1
  cases o with
  | thread g => exact absurd rfl (hth g)
  | bulk => exact bulk_steps (fun i _ ⟨_, hi⟩ => hc.no_kind hX (i := i) rfl hi) ho
  | arriveOn => exact arriveOn_steps (fun i _ _ ⟨_, hi⟩ => hc.no_kind hX (i := i) rfl hi) ho
  | mma =>
    refine (ho fun i hi => ?_).elim
    rcases hi with ⟨_, _, _, _, _, hi⟩ | ⟨_, _, hi⟩ | ⟨_, _, hi⟩ <;>
      exact (hc.no_kind hX (i := i) rfl hi).elim
  | clc => exact (ho fun i _ _ ⟨_, hi⟩ => (hc.no_kind hX (i := i) rfl hi).elim).elim
  | tensor => exact tensor_stepsE ha.step.sameTr hmax (P.tensorSources X hmax) ho
  | store => exact store_stepsE' ha.step.sameTr hmax (P.guard X hX) (P.storeSources X hmax) ho
  | commit => exact (ho fun i _ _ _ ⟨_, hi⟩ => (hc.no_kind hX (i := i) rfl hi).elim).elim
  | tmem => exact (ho fun i _ _ _ _ hi => (hc.no_kind hX (i := i) rfl hi).elim).elim

/-- **Progress by ranked descent**: every maximal execution is complete. -/
theorem progress_of2 : ProgressGoal K A L mem0 :=
  Descent.progress_of_steps (Descent.Obl L) (rank M) (fun _ _ hn => Descent.cover hn)
    fun _ o hmax ho => by
      cases o with
      | thread g => exact thread_steps2 ha hc P hs hmax ho
      | _ => exact async_steps2 ha hc P hmax (fun g h => by cases h) ho

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
