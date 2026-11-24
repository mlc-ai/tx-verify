-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Polls.PReady
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.P2
public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Blocked

@[expose] public section

/-! # The MMA warp's second P-ready polls

A released pending MMA thread at its second P-ready poll `p2Wait k lead` polls stage `k % 2`'s
second P-ready object of its CTA, with the parity of its successful polls of it
(`P2PollFacts.poll`). The object has a final state, since the thread is past its register
request (`state_of_time`). When that state's phase has the poll's parity, the phase is the
thread's successful polls, and a softmax thread of the stage in the pair, every election of which
returned its own lane, has made no more arrivals than it (`Score.p2_blocked`). That thread lags
the waiter (`P2PollFacts.lag_soft`), so it is a blocker (`Sched.blk_of_lags`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow MBarrier

noncomputable section

/-- **A released MMA thread at a second P-ready poll polls with a blocker when not ready.** -/
theorem p2_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hF : P2PollFacts L X) (hRC : Score.RouteCtx P L mem0 kernel asms X) {g : Nat}
    (hp : Frame.Pending L X g) (_hrel : Step.Released L X g)
    {d : Mma.D} (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hsite : ∃ k lead, d.site = .p2Wait k lead) : Sched.PollBlocked (timed L) X g := by
  obtain ⟨k, lead, hk⟩ := hsite
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨hw12, hlead, hpoll⟩ := hF.poll hg hσ hk
  have hst : k.val % 2 < 2 := Nat.mod_lt _ (by decide)
  have ht := regT_lt_mmaTime (L := L) (g := g) (.inr ⟨lead, hk⟩)
  obtain ⟨before, hb⟩ := state_of_time hpre hX hI hW hg hσ ht (.pReady2 ⟨k.val % 2, hst⟩)
  refine Sched.pollBlocked_of hpoll hb fun hpar => ?_
  obtain ⟨hph, y, hy, hly, hw8, hws, hsel, ha⟩ := Score.p2_blocked hRC hlead
    (cta_lt_grid hpre hg) hst ⟨hg, rfl, hw12⟩ (fun _ hr => InitFirst.fault_free (hs.2 X hX) hr)
    hb (by simpa using hpar)
  rw [hph] at ha
  exact Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg (ne_nil_of_role hσ) hσ hy
    (Score.sameCluster_of_pair hpre hy hg (hly.trans hlead.symm)).2.2
    (hF.lag_soft hg hy hσ hk hly hw8 hws hsel ha)

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
