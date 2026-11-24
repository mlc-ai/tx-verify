-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Polls.Role
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.SFull
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SFullBlocked

@[expose] public section

/-! # The S-full polls have a blocker

A softmax thread at its S-full wait (`sW`) polls its stage's S-full object of its CTA
(`SFullPollFacts.poll`), which has a final state (`state_of_time`). When that state's phase has
the poll's parity, the phase is at most the thread's successful polls of the object, and the
committing lane of warp 12 of the pair leader (a lane every election of which returned its own
lane) made no more commits to the stage's S-full object of its own CTA than the phase, or some
commit's notification is undelivered (`Score.sFull_blocked`, in a safe execution, whose
histories do not fault). In the first case the lane lags the thread (`SFullPollFacts.lag`) and
is a blocker (`Sched.blk_of_lags`); in the second the commit obligation is open. The enabling paths
of the object's reuse come from the context of the routes (`Score.RouteCtx`, built by
`SafeGlue2.routeCtx`), an input of this class. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- **A softmax thread at its S-full wait polls with a blocker when not ready.** -/
theorem sFull_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hF : SFullPollFacts L X) (hRC : Score.RouteCtx P L mem0 kernel asms X) {g : Nat}
    (hp : Frame.Pending L X g) (_hrel : Step.Released L X g)
    {d : Softmax.D} (hσ : St L X g (X.tr g).length = some (some (.inr (.softmax d))))
    (hsite : ∃ lp, d.site = .sW lp) : Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hg : g < L.threads := hp.1
  have hw : warpOf L g < 8 := (prologueFacts hpre hX).role_warp hg hσ
  have hst : warpOf L g / 4 < 2 := by omega
  obtain ⟨lp, hl⟩ := hsite
  have ht : Time.regT < stateTime L g (.inr (.softmax d)) := by
    simp only [stateTime, Time.softmax, hl]
    exact Time.fixed_lt (by decide)
  obtain ⟨before, hstate⟩ := state_of_time hpre hX hI hW hg hσ ht (.sFull ⟨_, hst⟩)
  refine Sched.pollBlocked_of (hF.poll hg hσ hl) hstate (fun hpar => ?_)
  obtain ⟨hph, y, hy, hwy, hcy, hself, hb⟩ := Score.sFull_blocked hRC hI.tc hg hw
    (fun _ hr => InitFirst.fault_free (hs.2 X hX) hr) hstate (by simpa using hpar)
  rcases hb with hle | hobl
  · have hcl : leadCta (ctaOf L y) = leadCta (ctaOf L g) := by rw [hcy]; unfold leadCta; omega
    exact Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg (ne_nil_of_role hσ) hσ hy
      (Score.sameCluster_of_pair hpre hy hg hcl).2.2
      (hF.lag hg hσ hl hy hwy hcy hself (le_trans hle hph))
  · exact .inl ⟨.commit, .inl rfl, hobl⟩

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
