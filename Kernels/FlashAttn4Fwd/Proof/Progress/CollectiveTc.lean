-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Tc
public import Lemmas.Step.CtaBarNamed
public import Lemmas.Kernel.Progress.Bar

@[expose] public section

/-! # Progress at a warp-collective `tcgen05` event

A pending thread whose last event is its `k`-th warp-collective `tcgen05` event, which some lane
of its warp has not executed (`TcWait`, DEP-TC-COLLECTIVE), steps (`tc_steps`). That lane has
made at most `k` such events. It has not exited: an exit with at most `k` of them, in the warp of
a lane at its `k`-th, is unsafe (`TcUnsafe`, ERR-ALIGNED-MISMATCH). So it is pending, and it is at
a state no later than the blocked thread's state before the event (`TcWaitFacts.lag`), which is
earlier than the blocked thread's state after it (`TcWaitFacts.after`): the lane ranks below the
blocked thread. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread that has made more than `k` warp-collective `tcgen05` events has a `k`-th. -/
theorem tcK_of_lt {h k : Nat} (hk : k < (X.tr h).countP isTcColl) : ∃ j, X.TcK (h, j) k := by
  obtain ⟨j, e, hj, he, hjk⟩ := NamedBar.exists_ordinal isTcColl (X.tr h) hk
  exact ⟨j, ⟨e, hj, he⟩, hjk⟩

/-- **Progress at a warp-collective `tcgen05` event.** A pending thread whose last event is a
warp-collective `tcgen05` event that some lane of its warp has not executed steps: that lane is
pending and earlier. -/
theorem tc_steps (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (htr : Frame.Tracked (code L) X) (hw : TcWaitFacts L X) (hmax : Maximal L kernel asms mem0 X)
    {g : Nat} (hp : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (htw : Sched.TcWait L X g) :
    Sched.Steps (timed L) mem0 X (.thread g) := by
  obtain ⟨k, hlen, hk, hnd⟩ := htw
  have hX := hmax.1
  have hg := hp.1
  have hsafe := hs.2 X hX
  have hub := Sched.safe_noUb hsafe
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  obtain ⟨h, hh, hsw, hnh⟩ : ∃ h, h < L.threads ∧ SameWarp L g h ∧ ∀ j, ¬ X.TcK (h, j) k := by
    by_contra hcon
    push Not at hcon
    exact hnd fun h hh hw => hcon h hh hw
  have hle : (X.tr h).countP isTcColl ≤ k := by
    by_contra hlt
    obtain ⟨j, hj⟩ := tcK_of_lt (Nat.lt_of_not_le hlt)
    exact hnh j hj
  have hnx : ∀ j pc, X.get (h, j) ≠ some ⟨pc, .exit⟩ := by
    intro j pc hj
    have htc : ¬ AlignedMismatch L kernel X := fun h => hsafe (by simp [Unsafe, h])
    obtain ⟨ev, hev, hcoll⟩ := hk.1
    refine htc ⟨.tc, .inr ⟨(g, (X.tr g).length - 1), (h, j), ev, hsw, hev, hcoll, rfl,
      ⟨pc, hj⟩, ?_⟩⟩
    show (X.tr h).countP isTcColl ≤ ((X.tr g).take ((X.tr g).length - 1)).countP isTcColl
    rw [hk.2]
    exact hle
  have hph := Sched.pending_of_noExit hX hg hne hh (Sched.cluster_of_sameWarp hsw) hnx
  obtain ⟨ev, hev, -⟩ := hk.1
  obtain ⟨d, hd⟩ := Frame.state_of_noUb (prologueFacts hpre hX).sound hX htr hub hev
  have h1 : endTime L X h ≤ stateTime L g d := hw.lag hg hh hsw hk hd hle
  have h2 : stateTime L g d < endTime L X g :=
    Sched.threadTime_after (M := timed L) hlen hd (hw.after hg hk hd)
  exact Sched.earlier_steps hmax hrel hph (by omega)

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
