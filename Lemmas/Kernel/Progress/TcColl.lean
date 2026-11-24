-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Kernel.Progress.Bar
public import Lemmas.Kernel.Goals
public import Lemmas.Step.CtaBarNamed

@[expose] public section

/-! # Progress at a warp-collective `tcgen05` event

A proof tool, generic over the kernel (promoted from FA4's `Proof/Progress/CollectiveTc.lean`).
A pending thread whose last event is its `k`-th warp-collective `tcgen05` event, which some lane
of its warp has not executed (`TcWait`, DEP-TC-COLLECTIVE), steps (`Sched.tc_steps`). That lane
has made at most `k` such events. It has not exited: an exit with at most `k` of them, in the warp
of a lane at its `k`-th, is unsafe (ERR-ALIGNED-MISMATCH). So it is pending, and the kernel's time
table places it no later than the blocked thread's state before the event (`hlag`), which is
earlier than the blocked thread's state after it (`hafter`): the lane ranks below the blocked
thread. -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- A thread that has made more than `k` warp-collective `tcgen05` events has a `k`-th. -/
theorem tcK_of_lt {h k : Nat} (hk : k < (X.tr h).countP isTcColl) : ∃ j, X.TcK (h, j) k := by
  obtain ⟨j, e, hj, he, hjk⟩ := NamedBar.exists_ordinal isTcColl (X.tr h) hk
  exact ⟨j, ⟨e, hj, he⟩, hjk⟩

/-- **Progress at a warp-collective `tcgen05` event.** A pending thread whose last event is a
warp-collective `tcgen05` event that some lane of its warp has not executed steps: that lane is
pending and earlier. -/
theorem tc_steps (hC : ∀ g < L.threads, (M.code g).Sound) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X)
    (hlag : ∀ {g h j k : Nat} {d : (M.code g).D}, g < L.threads → h < L.threads →
      SameWarp L g h → X.TcK (g, j) k → Frame.stateAt M.code X g j = some (some d) →
      (X.tr h).countP isTcColl ≤ k → threadTime M X h ≤ M.time g d)
    (hafter : ∀ {g j k : Nat} {d : (M.code g).D}, g < L.threads → X.TcK (g, j) k →
      Frame.stateAt M.code X g j = some (some d) →
      (∃ d', Frame.stateAt M.code X g (j + 1) = some (some d') ∧ M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g (j + 1) = none)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) (htw : TcWait L X g) : Steps M mem0 X (.thread g) := by
  obtain ⟨k, hlen, hk, hnd⟩ := htw
  have hX := hmax.1
  have hg := hp.1
  have hsafe := hs.2 X hX
  have hub := safe_noUb hsafe
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
    have htc : ¬ AlignedMismatch L K X := fun h => hsafe (by simp [Unsafe, h])
    obtain ⟨ev, hev, hcoll⟩ := hk.1
    refine htc ⟨.tc, .inr ⟨(g, (X.tr g).length - 1), (h, j), ev, hsw, hev, hcoll, rfl,
      ⟨pc, hj⟩, ?_⟩⟩
    show (X.tr h).countP isTcColl ≤ ((X.tr g).take ((X.tr g).length - 1)).countP isTcColl
    rw [hk.2]
    exact hle
  have hph := pending_of_noExit hX hg hne hh (cluster_of_sameWarp hsw) hnx
  obtain ⟨ev, hev, -⟩ := hk.1
  obtain ⟨d, hd⟩ := Frame.state_of_noUb hC hX htr hub hev
  have h1 : threadTime M X h ≤ M.time g d := hlag hg hh hsw hk hd hle
  have h2 : M.time g d < threadTime M X g := threadTime_after hlen hd (hafter hg hk hd)
  exact earlier_steps hmax hrel hph (by omega)

end

end PTX.Sched
