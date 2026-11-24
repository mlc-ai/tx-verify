-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Rank

@[expose] public section

/-! # The mbarrier polls: from a blocker in the execution to `MbarAt`

A released pending thread `g` whose next event polls an object `m` steps when, should the
object's final phase have the poll's parity, the execution itself has a blocker of the thread
(`Blk`): an open asynchronous obligation, or a pending thread earlier than `g`. That blocker
stays one in the execution with the failed poll appended (`Step.failedPoll`), which changes
only `g`'s trace and `m`'s history (`blk_failedPoll`): so the poll is an `MbarAt` with the
blocker time one below the thread's (`mbarAt_of`). Each wait class of a kernel proves
`PollBlocked`, from two kinds of thread facts:

* `PollsOn K A L X g m δ`: the thread's next event polls `m` (by local steps it reaches a wait on
  `m`, successful or not, at one position and parity), with the parity of its successful polls of
  `m` plus `δ` (`pollBlocked_of`);
* `Lags M X y b`: in an execution without undefined behaviour, a producer `y` has not exited
  and is earlier than the waiter's time `b`; a lagging producer of the waiter's cluster is a
  blocker (`blk_of_lags`). -/

namespace PTX.Sched

open PTX PTX.Flow MBarrier

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

section
variable (M : Timed K A L)

/-- **A blocker of thread `g` in `X`**: an open asynchronous obligation, or a pending thread
earlier than `g`. -/
def Blk (X : Execution) (g : Nat) : Prop :=
  (∃ o, (o = .commit ∨ o = .mma ∨ o = .tensor ∨ o = .store ∨
      o = .arriveOn) ∧ Descent.Obl L X o) ∨
    ∃ h, Frame.Pending L X h ∧ threadTime M X h < threadTime M X g

/-- **Thread `g` polls an object with a blocker when not ready**: its next event polls `m`
(at `pcw`, parity `par`), `m` has a state, and when that state's phase has the poll's parity,
`g` has a blocker. -/
def PollBlocked (X : Execution) (g : Nat) : Prop :=
  ∃ (m : Loc) (pcw par : Nat), (∀ t, Run K A L g {} (X.tr g) (some t) → ∀ ok : Bool,
      ∃ t1 u sc, Relation.ReflTransGen (Tau K A L g) t t1 ∧
        EStep K A L g t1 ⟨pcw, .wait m par ok true sc⟩ (some u)) ∧
    ∃ before, stateBefore (X.objects m) (X.objects m).length = some before ∧
      (before.phase % 2 = par % 2 → Blk M X g)

/-- **Thread `y` lags a waiter at time `b`**: when the execution has no undefined behaviour, `y`
has not exited, and its time is earlier than `b`. -/
def Lags (X : Execution) (y b : Nat) : Prop :=
  ¬ HasUb X → (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧ threadTime M X y < b

end

/-- **Thread `g`'s next event polls `m`**, with the parity of its successful polls of `m` plus
`δ`: from every run of its trace, by local steps, it reaches a wait on `m` at position `pcw` with
parity `par`, for either outcome. -/
def PollsOn (K : Kernel) (A : List Assumption) (L : Launch) (X : Execution) (g : Nat) (m : Loc)
    (δ : Nat) : Prop :=
  ∃ pcw par : Nat, par % 2 = (okPolls m (X.tr g) + δ) % 2 ∧
    ∀ t, Run K A L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau K A L g) t t1 ∧
      EStep K A L g t1 ⟨pcw, .wait m par ok true sc⟩ (some u)

variable {M : Timed K A L}
  {X : Execution} {g : Nat}

/-- An event of `X` is one of the execution with a failed poll appended. -/
theorem get_failedPoll {pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope} {before : State}
    {i : EvId} {e : Event} (h : X.get i = some e) :
    (Step.failedPoll X g pc p m acq sc before).get i = some e := by
  obtain ⟨h1, k⟩ := i
  change ((Step.failedPoll X g pc p m acq sc before).tr h1)[k]? = some e
  change (X.tr h1)[k]? = some e at h
  rw [Step.failedPoll_tr]
  split_ifs with hh
  · subst hh
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
    exact h
  · exact h

/-- An open asynchronous obligation stays open when a failed poll is appended. -/
theorem obl_failedPoll {pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope} {before : State}
    {o : Descent.Obligation} (ho : o = .commit ∨ o = .mma ∨ o = .tensor ∨ o = .store ∨
      o = .arriveOn)
    (h : Descent.Obl L X o) : Descent.Obl L (Step.failedPoll X g pc p m acq sc before) o := by
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [Descent.Obl] at h ⊢ <;>
    intro hall <;> apply h
  · intro i s rank m' ⟨pc', he⟩ ht
    exact hall i s rank m' ⟨pc', get_failedPoll he⟩ ht
  · rintro i (⟨d, s, accum, mask, pc', he⟩ | ⟨c, pc', he⟩ | ⟨s, pc', he⟩)
    · exact hall i (.inl ⟨d, s, accum, mask, pc', get_failedPoll he⟩)
    · exact hall i (.inr (.inl ⟨c, pc', get_failedPoll he⟩))
    · exact hall i (.inr (.inr ⟨s, pc', get_failedPoll he⟩))
  · intro i a s ⟨pc', he⟩
    exact hall i a s ⟨pc', get_failedPoll he⟩
  · intro i a s ⟨pc', he⟩
    exact hall i a s ⟨pc', get_failedPoll he⟩
  · intro i m' noinc ⟨pc', he⟩
    exact hall i m' noinc ⟨pc', get_failedPoll he⟩

/-- **A blocker stays one when a failed poll is appended**, no later than one below the
thread's time. -/
theorem blk_failedPoll {pc p : Nat} {m : Loc} {acq : Bool} {sc : MbarScope} {before : State}
    (h : Blk M X g) :
    BlockerBy M (Step.failedPoll X g pc p m acq sc before) (threadTime M X g - 1) := by
  rcases h with ⟨o, ho, hobl⟩ | ⟨h, hp, hlt⟩
  · exact .inl ⟨o, ho, obl_failedPoll ho hobl⟩
  · have hne : h ≠ g := fun he => by subst he; omega
    have htr : (Step.failedPoll X g pc p m acq sc before).tr h = X.tr h := by
      simp only [Step.failedPoll_tr, hne, ↓reduceIte]
    refine .inr ⟨h, ⟨hp.1, ?_, ?_⟩, ?_⟩
    · rintro ⟨h1, h2⟩
      exact hp.2.1 ⟨by rw [← htr]; exact h1, h2⟩
    · rw [htr]; exact hp.2.2
    · rw [threadTime_congr htr]; omega

/-- **A poll with a blocker when not ready is an `MbarAt`**, with the blocker time one below the
thread's. -/
theorem mbarAt_of (h : PollBlocked M X g) : MbarAt M mem0 X g (threadTime M X g - 1) := by
  obtain ⟨m, pcw, par, hpoll, before, hstate, hblk⟩ := h
  refine ⟨m, pcw, par, fun _ => True, before, fun t hr ok => ?_, hstate,
    fun sc _ hp _ => blk_failedPoll (hblk hp)⟩
  obtain ⟨t1, u, sc, h1, h2⟩ := hpoll t hr ok
  exact ⟨t1, u, sc, h1, h2, fun _ => trivial⟩

/-- **A poll of `m` with a blocker when not ready**, from `PollsOn`, the object's state, and a
blocker whenever the final phase has the parity of the thread's successful polls plus `δ`. -/
theorem pollBlocked_of {m : Loc} {δ : Nat} (hp : PollsOn K A L X g m δ) {before : State}
    (hstate : stateBefore (X.objects m) (X.objects m).length = some before)
    (hblk : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2 → Blk M X g) :
    PollBlocked M X g := by
  obtain ⟨pcw, par, hpar, hpoll⟩ := hp
  exact ⟨m, pcw, par, hpoll, before, hstate, fun h => hblk (by omega)⟩

/-- **A lagging producer of the waiter's cluster is a blocker.** -/
theorem blk_of_lags (hX : Consistent L K A mem0 X) (hub : ¬ HasUb X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d))
    {y : Nat} (hy : y < L.threads)
    (hc : L.clusterOfCta (y / L.block) = L.clusterOfCta (g / L.block))
    (hl : Lags M X y (M.time g d)) : Blk M X g := by
  refine .inr ⟨y, pending_of_noExit hX hg hne hy hc (hl hub).1, ?_⟩
  rw [threadTime_of hσ]
  exact (hl hub).2

end

end PTX.Sched
