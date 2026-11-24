-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcGroup
public import Lemmas.CtaBarrier.CtaBarrierRoundHistory

namespace PTX.Tests.TcCommitSafety
noncomputable section

private def launch : Launch :=
  { grid := 2, block := 1, params := fun _ => none, clusterSize := 2 }
private def localMbar : Loc := ⟨.shared, 0, 40⟩
private def peerMbar : Loc := ⟨.shared, 1, 40⟩
private def spec : TcCommit.Spec := ⟨.two, localMbar, 3, 0, 2⟩
private def X : Execution where
  tr := fun g => if g = 0 then [⟨0, .mbInit localMbar 1⟩, ⟨1, .tc (.commit spec)⟩]
    else if g = 1 then [⟨0, .exit⟩] else []
  rf := fun _ _ => none
private theorem issue : X.Commit (0, 1) spec := ⟨1, rfl⟩
private def K : Kernel := { name := "k", params := [], code := [] }

-- The local target can be ready while its own arrival is still pending: the target is
-- initialized and published, and its CTA has not exited, so the pending arrival is no
-- lifetime violation.
example : ∃ init count, X.MbInit init localMbar count ∧
    InitPublished launch X init (0, 1) localMbar := by
  refine ⟨(0, 0), 1, ⟨0, rfl⟩, Or.inl ?_⟩
  exact Relation.TransGen.single (Or.inl ⟨rfl, by decide, by decide⟩)
example : ¬ CtaExited launch X localMbar.cta := by
  intro h
  obtain ⟨pc, hp⟩ := h 0 (by decide) rfl
  cases hp

private theorem no_peer_init (i : EvId) (count : Nat) : ¬ X.MbInit i peerMbar count := by
  obtain ⟨g, n⟩ := i
  intro h
  by_cases hg : g = 0
  · subst g
    cases n with
    | zero => simp [Execution.MbInit, Execution.get, X, localMbar, peerMbar] at h
    | succ n => cases n <;> simp [Execution.MbInit, Execution.get, X, peerMbar] at h
  · by_cases hg1 : g = 1
    · subst g
      cases n <;> simp [Execution.MbInit, Execution.get, X, peerMbar] at h
    · simp [Execution.MbInit, Execution.get, X, hg, hg1] at h

-- Initializing one address does not initialize the same offset in its peer CTA.
example : MbarUninit launch X :=
  tcCommit_uninitialized_uninit issue (rank := 1) rfl no_peer_init

private theorem peer_exited : CtaExited launch X 1 := by
  intro g hg hc
  have he : g = 1 := by simpa [launch] using hc
  subst g
  exact ⟨0, rfl⟩

-- Independently of initialization, an exited owner cannot retain a pending arrival.
example : SharedLifetimeUnsafe launch K [] X :=
  tcCommit_pending_at_exit_unsafe issue (rank := 1) rfl peer_exited (by simp [X])

-- Pending notification already creates the remote-startup obligation.
example (hn : ¬ PeerSharedStarted launch K [] X (.async (0, 1) (.tcNotify 1)) 1) :
    SharedLifetimeUnsafe launch K [] X :=
  ⟨_, _, tcCommit_use issue (rank := 1) rfl, .inl ⟨by decide, hn⟩⟩

-- Every target is an mbarrier use, so the bytewise storage rule covers peer targets.
example : X.UsesMbar (0, 1) peerMbar := .inr (.inr (.inr (Or.inl ⟨spec, 1, issue, rfl⟩)))

private theorem pair : SameCtaGroup launch .two ((0, 0) : EvId).1 1 := by
  unfold SameCtaGroup CtaInCluster Launch.ctaGroupRanks CtaGroup.size; decide

private theorem pairUse {Y : Execution} {s : TcCommit.Spec} (hi : Y.Commit (0, 0) s)
    (hg : s.group = .two) : SharedUse launch Y (.thread (0, 0)) 1 :=
  .inr (.inl ⟨(0, 0), s, rfl, hi, by rw [hg]; exact pair⟩)

-- Selecting no targets cannot waive the issuing pair's startup requirement.
example (Y : Execution) (s : TcCommit.Spec) (hi : Y.Commit (0, 0) s) (hg : s.group = .two)
    (hn : ¬ PeerSharedStarted launch K [] Y (.thread (0, 0)) 1) :
    SharedLifetimeUnsafe launch K [] Y :=
  ⟨_, _, pairUse hi hg, .inl ⟨by decide, hn⟩⟩

-- Completion of the issue must precede the peer's exit, independently of notification.
example (Y : Execution) (s : TcCommit.Spec) (hi : Y.Commit (0, 0) s) (hg : s.group = .two)
    (h : ¬ SharedLifetimeUnsafe launch K [] Y) (hexit : CtaExited launch Y 1) :
    SharedFinished launch K [] Y (.thread (0, 0)) 1 :=
  Classical.byContradiction fun hn => h ⟨_, _, pairUse hi hg, .inr ⟨hexit, hn⟩⟩

-- A group-2 issue needs its whole CTA pair inside the cluster.
example (s : TcCommit.Spec) (hg : s.group = .two) :
    ¬ TcCommitIssueSafe { grid := 2, block := 1, params := fun _ => none } (0, 0) s := by
  rintro ⟨_, _, hb⟩
  rw [hg] at hb
  exact hb (by decide)

-- A group-1 issue has no peer obligation.
example (s : TcCommit.Spec) (hg : s.group = .one) (peer : Nat)
    (hp : SameCtaGroup launch s.group (((0, 0) : EvId).1 / launch.block) peer) :
    peer = ((0, 0) : EvId).1 / launch.block := by
  rw [hg] at hp
  exact (sameCtaGroup_one (Launch.oneDimLaunch_clusterGridValid (by
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide⟩)) hp).symm

end
end PTX.Tests.TcCommitSafety
