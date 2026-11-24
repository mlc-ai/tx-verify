-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Obligation
public import Lemmas.Kernel.NextInOrder

@[expose] public section

/-! # Ranks by the time of a thread's machine state

A kernel's progress argument by descent (`Descent.progress_of_steps`) ranks its obligations. Here
the rank of a pending thread is read off a time table (`Timed`: a site machine `M.code g` per
thread and a time `M.time g d` for each of its abstract states `d`), in a sequential schedule the
kernel chooses; the layers above the thread layer have no other handle on a thread's place in the
schedule.

* `threadTime M X g`: the time of the thread's state at its trace's end; when its machine has
  stopped after its last event (its run reaches undefined behaviour by local steps), one more
  than the time of its state before that event (`threadTime_stop`).
* `rank M X`: a pending thread ranks at twice its time, plus one while its last event blocks
  (`Step.Released` fails). An asynchronous copy or MMA ranks 1, a commit's delivery 2, a tensor
  store 0, below every thread at a wait of time at least 2 (`rank_async_lt`); the paired Tensor
  Memory requests rank above every thread (`rank_thread_lt_tmem`).
* A thread steps when a blocker is earlier than it: at an mbarrier poll, a blocker of the
  execution with the failed poll appended (`MbarAt`, `mbar_at_steps`); at a blocking last event,
  an open asynchronous obligation or a pending thread that is earlier, or released at the same
  time (`Lagging`, `lagging_steps`, `earlier_steps`), or an execution with the same traces that
  releases it (`same_trace_steps`).
* A thread with no exit event of a cluster in which some thread has an event is pending
  (`pending_of_noExit`). -/

namespace PTX.Sched

open PTX PTX.Flow MBarrier Classical

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- A site machine for every thread and a time for each of its abstract states. -/
structure Timed (K : Kernel) (A : List Assumption) (L : Launch) where
  /-- The site machine of thread `g`. -/
  code : (g : Nat) → Flow.Code K A L g
  /-- The time of a state of thread `g`'s machine. -/
  time : (g : Nat) → (code g).D → Nat

section
variable (M : Timed K A L)

/-- The time of thread `g`'s next event: its state's time. When its machine has stopped, one
more than the time of its state before its last event, so that a lane it waits for, no later
than that state, ranks below it (`0` otherwise). -/
def threadTime (X : Execution) (g : Nat) : Nat :=
  match Frame.stateAt M.code X g (X.tr g).length with
  | some (some d) => M.time g d
  | some none => 0
  | none =>
    match Frame.stateAt M.code X g ((X.tr g).length - 1) with
    | some (some d) => M.time g d + 1
    | _ => 0

/-- A time above every thread's. -/
def topTime (X : Execution) : Nat :=
  1 + ∑ h ∈ Finset.range L.threads, threadTime M X h

/-- The rank of an obligation. -/
def rank (X : Execution) : Descent.Obligation → Nat
  | .thread g => 2 * threadTime M X g + (if Step.Released L X g then 0 else 1)
  | .commit => 2
  | .store => 0
  | .tmem => 2 * topTime M X + 2
  | _ => 1

/-- The descent step of an obligation, under the ranks of the time table. -/
abbrev Steps (mem0 : Mem0) (X : Execution) (o : Descent.Obligation) : Prop :=
  Descent.Steps L K A mem0 (Descent.Obl L) (rank M) X o

/-- **A blocker no later than `b`**: an open asynchronous obligation, or a pending thread whose
next event is at time `b` or earlier. -/
def BlockerBy (Y : Execution) (b : Nat) : Prop :=
  (∃ o, (o = .commit ∨ o = .mma ∨ o = .tensor ∨ o = .store ∨
      o = .arriveOn) ∧ Descent.Obl L Y o) ∨
    ∃ h, Frame.Pending L Y h ∧ threadTime M Y h ≤ b

/-- **A released thread at an mbarrier wait with blockers no later than `b`.** Its next event
polls barrier `m` with parity `par` (a failed poll under the scope condition `Q`), the barrier has
a state, and in the execution with a failed poll appended, when the barrier is not ready and that
execution is maximal, the wait has a blocker no later than `b`. -/
def MbarAt (mem0 : Mem0) (X : Execution) (g b : Nat) : Prop :=
  ∃ (m : Loc) (pcw par : Nat) (Q : MbarScope → Prop) (before : State),
    (∀ t, Run K A L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau K A L g) t t1 ∧
      EStep K A L g t1 ⟨pcw, .wait m par ok true sc⟩ (some u) ∧ (ok = false → Q sc)) ∧
    stateBefore (X.objects m) (X.objects m).length = some before ∧
    ∀ sc, Q sc → before.phase % 2 = par % 2 →
      Maximal L K A mem0 (Step.failedPoll X g pcw par m true sc before) →
      BlockerBy M (Step.failedPoll X g pcw par m true sc before) b

/-- **A blocker of a blocked last event, in the execution itself**: an open asynchronous
obligation, or a pending thread that is earlier, or released at the same time. -/
def Lagging (X : Execution) (g : Nat) : Prop :=
  (∃ o, (o = .commit ∨ o = .mma ∨ o = .tensor ∨ o = .store ∨
      o = .arriveOn) ∧ Descent.Obl L X o) ∨
    ∃ h, Frame.Pending L X h ∧ (threadTime M X h < threadTime M X g ∨
      (threadTime M X h = threadTime M X g ∧ Step.Released L X h))

end

variable {M : Timed K A L}
  {X Y : Execution} {g h : Nat}

theorem threadTime_of {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) :
    threadTime M X g = M.time g d := by
  simp [threadTime, hσ]

/-- A thread whose machine has stopped after its last event is one later than its state before
that event. -/
theorem threadTime_stop {d : (M.code g).D}
    (hd : Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d))
    (hσ : Frame.stateAt M.code X g (X.tr g).length = none) : threadTime M X g = M.time g d + 1 := by
  simp [threadTime, hσ, hd]

/-- The machine state, and so the time, of a thread depends on its trace only. -/
theorem threadTime_congr (htr : Y.tr g = X.tr g) : threadTime M Y g = threadTime M X g := by
  simp only [threadTime, Frame.stateAt, htr]

/-- A thread ranks at most one above twice its time. -/
theorem rank_thread_le : rank M X (.thread g) ≤ 2 * threadTime M X g + 1 := by
  simp only [rank]
  split <;> omega

/-- A thread whose last event is released ranks at twice its time. -/
theorem rank_released (hr : Step.Released L X g) :
    rank M X (.thread g) = 2 * threadTime M X g := by
  simp [rank, hr]

/-- A thread whose last event blocks ranks one above twice its time. -/
theorem rank_unreleased (hr : ¬ Step.Released L X g) :
    rank M X (.thread g) = 2 * threadTime M X g + 1 := by
  simp [rank, hr]

/-- **A thread of an earlier time ranks below**, blocked or not. -/
theorem rank_lt_of_time_lt {τ : Nat} (hlt : threadTime M Y h < τ) :
    rank M Y (.thread h) < 2 * τ := by
  have := rank_thread_le (M := M) (X := Y) (g := h)
  omega

/-- A thread no later than `τ`, earlier or released, ranks at most `2 τ`. -/
theorem rank_le_of_time {τ : Nat}
    (hle : threadTime M Y h < τ ∨ (threadTime M Y h = τ ∧ Step.Released L Y h)) :
    rank M Y (.thread h) ≤ 2 * τ := by
  rcases hle with hlt | ⟨heq, hr⟩
  · exact (rank_lt_of_time_lt hlt).le
  · rw [rank_released hr, heq]

/-- The asynchronous obligations rank below every thread at time at least 2. -/
theorem rank_async_lt {τ : Nat} (hτ : 2 ≤ τ) {o : Descent.Obligation}
    (ho : o = .commit ∨ o = .mma ∨ o = .tensor ∨ o = .store ∨
      o = .arriveOn) : rank M Y o < 2 * τ := by
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rank] <;> omega

/-- **The store obligation ranks below every blocked thread.** -/
theorem rank_store_lt (hr : ¬ Step.Released L X g) :
    rank M X .store < rank M X (.thread g) := by
  rw [rank_unreleased hr]
  simp only [rank]
  omega

/-- Every thread's time is below the top. -/
theorem threadTime_lt_top (hh : h < L.threads) : threadTime M X h < topTime M X := by
  have := Finset.single_le_sum (f := threadTime M X) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hh)
  simp only [topTime]
  omega

/-- **The paired Tensor Memory obligation ranks above every thread.** -/
theorem rank_thread_lt_tmem (hh : h < L.threads) : rank M X (.thread h) < rank M X .tmem := by
  have h1 := rank_thread_le (M := M) (X := X) (g := h)
  have h2 := threadTime_lt_top (M := M) (X := X) hh
  simp only [rank] at h1 ⊢
  omega

/-! ### Blockers -/

/-- A blocker no later than `b < τ` ranks below twice `τ`. -/
theorem BlockerBy.rank_lt {b τ : Nat} (hb : b < τ) (hτ : 2 ≤ τ) (hB : BlockerBy M Y b) :
    ∃ o, Descent.Obl L Y o ∧ rank M Y o < 2 * τ := by
  rcases hB with ⟨o, ho, hobl⟩ | ⟨h, hp, hle⟩
  · exact ⟨o, hobl, rank_async_lt hτ ho⟩
  · exact ⟨.thread h, hp, rank_lt_of_time_lt (Nat.lt_of_le_of_lt hle hb)⟩

/-- A blocker no later than `b` is one no later than any `b' ≥ b`. -/
theorem BlockerBy.mono {b b' : Nat} (hb : b ≤ b') (hB : BlockerBy M Y b) :
    BlockerBy M Y b' := by
  rcases hB with h | ⟨h, hp, hle⟩
  · exact .inl h
  · exact .inr ⟨h, hp, Nat.le_trans hle hb⟩

theorem MbarAt.mono {b b' : Nat} (hb : b ≤ b') (h : MbarAt M mem0 X g b) :
    MbarAt M mem0 X g b' := by
  obtain ⟨m, pcw, par, Q, before, hpoll, hstate, hB⟩ := h
  exact ⟨m, pcw, par, Q, before, hpoll, hstate, fun sc hq hp hY => (hB sc hq hp hY).mono hb⟩

/-- **A released thread at an mbarrier wait steps**, when its blockers are earlier than its
time. -/
theorem mbar_at_steps (hA : Assumption.WfStep (fun _ => true) L K mem0 A) (hub : ¬ HasUb X)
    (hmax : Maximal L K A mem0 X) (hp : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hne : X.tr g ≠ []) {b : Nat} (h : MbarAt M mem0 X g b) (hb : b < threadTime M X g)
    (h2 : 2 ≤ threadTime M X g) : Steps M mem0 X (.thread g) := by
  obtain ⟨m, pcw, par, Q, before, hpoll, hstate, hB⟩ := h
  refine Descent.mbar_wait_steps_inOrder hA hub hmax hp hrel hne hpoll hstate ?_
  intro sc hq hpar hY
  rw [rank_released hrel]
  exact (hB sc hq hpar hY).rank_lt hb h2

/-- A blocker no later than `b`, earlier than the blocked thread, lags it. -/
theorem Lagging.of_by {b : Nat} (h : BlockerBy M X b) (hb : b < threadTime M X g) :
    Lagging M X g := by
  rcases h with h | ⟨h, hp, hle⟩
  · exact .inl h
  · exact .inr ⟨h, hp, .inl (Nat.lt_of_le_of_lt hle hb)⟩

/-- **A blocked thread with a lagging blocker steps**: the blocker ranks below it. -/
theorem lagging_steps (hmax : Maximal L K A mem0 X) (hnr : ¬ Step.Released L X g)
    (h2 : 1 ≤ threadTime M X g) (hl : Lagging M X g) : Steps M mem0 X (.thread g) := by
  right
  refine ⟨X, ?_⟩
  rw [rank_unreleased hnr]
  rcases hl with ⟨o, ho, hobl⟩ | ⟨h, hp, hle⟩
  · refine ⟨o, hmax, hobl, ?_⟩
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [rank] <;> omega
  · exact ⟨.thread h, hmax, hp, Nat.lt_succ_of_le (rank_le_of_time hle)⟩

/-- **A blocked thread steps when a pending thread is earlier.** -/
theorem earlier_steps (hmax : Maximal L K A mem0 X) (hnr : ¬ Step.Released L X g)
    (hp : Frame.Pending L X h) (hlt : threadTime M X h < threadTime M X g) :
    Steps M mem0 X (.thread g) :=
  lagging_steps hmax hnr (by omega) (.inr ⟨h, hp, .inl hlt⟩)

/-- **A blocked thread that an execution with the same traces releases steps**: there it ranks
one lower. -/
theorem same_trace_steps (hp : Frame.Pending L X g) (hne : X.tr g ≠ [])
    (hnr : ¬ Step.Released L X g) (hY : Maximal L K A mem0 Y) (htr : Y.tr = X.tr)
    (hrel : Step.Released L Y g) : Steps M mem0 X (.thread g) := by
  have hpY : Frame.Pending L Y g := by
    refine ⟨hp.1, fun hc => hne ?_, ?_⟩
    · rw [← htr]; exact hc.1
    · rw [htr]; exact hp.2.2
  refine .inr ⟨Y, .thread g, hY, hpY, ?_⟩
  rw [rank_released hrel, rank_unreleased hnr, threadTime_congr (congrFun htr g)]
  omega

/-! ### Pending threads -/

/-- A safe execution has no undefined behaviour. -/
theorem safe_noUb (hs : ¬ Unsafe L K A mem0 X) : ¬ HasUb X :=
  fun h => hs (by unfold Unsafe; exact .inl h)

/-- A thread of a cluster in which some thread has an event is not canceled. -/
theorem not_canceled_of_peer (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) (hc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block)) :
    ¬ ClcCanceled L X h := by
  rintro ⟨-, r, hr⟩
  obtain ⟨i, s, ts, -, his, -⟩ := hX.clc.canceled_has_issue hr
  rw [hc] at hr
  exact hX.clc.running_not_canceled ⟨i, s, ts, his⟩ hg hne hr

/-- Two threads of a warp are in one cluster. -/
theorem cluster_of_sameWarp (hw : SameWarp L g h) :
    L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block) := by
  rw [hw.1.2.2]

/-- A thread whose last event is an exit has the exit at its last position. -/
theorem exit_get {pc : Nat} (hl : (X.tr h).getLast? = some ⟨pc, .exit⟩) :
    X.get (h, (X.tr h).length - 1) = some ⟨pc, .exit⟩ := by
  change (X.tr h)[(X.tr h).length - 1]? = _
  rw [← List.getLast?_eq_getElem?]
  exact hl

/-- A thread with no exit event is pending, when a thread of its cluster has an event. -/
theorem pending_of_noExit (hX : Consistent L K A mem0 X) (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hh : h < L.threads) (hc : L.clusterOfCta (h / L.block) = L.clusterOfCta (g / L.block))
    (hnx : ∀ j pc, X.get (h, j) ≠ some ⟨pc, .exit⟩) : Frame.Pending L X h :=
  ⟨hh, not_canceled_of_peer hX hg hne hc, fun pc hl => hnx _ pc (exit_get hl)⟩

end

end PTX.Sched
