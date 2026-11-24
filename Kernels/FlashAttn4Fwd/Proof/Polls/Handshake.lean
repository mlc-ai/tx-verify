-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Polls.Role
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Handshake
public import Kernels.FlashAttn4Fwd.Proof.Protocol.HandshakeBlocked
public import Kernels.FlashAttn4Fwd.Proof.Protocol.HsInitProof

@[expose] public section

/-! # The deallocation handshake poll has a blocker

An MMA lane at `waitDealloc` polls its CTA's handshake barrier at parity 0, with no successful
poll of it yet (`HandshakePollFacts.poll`); the barrier has a final state (`state_of_time`). When
that state's phase is even, some lane of the other CTA's MMA warp has made no arrival on the
barrier (`TmemAlloc.handshake_short`, with the barrier initialized first,
`HsInitProof.hsInit`), so it lags the lane (`HandshakePollFacts.lag`) and is a blocker
(`Sched.blk_of_lags`): both CTAs are of one cluster. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- **An MMA lane at the handshake poll polls with a blocker when not ready.** -/
theorem handshake_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hF : HandshakePollFacts L X) {g : Nat} (hp : Frame.Pending L X g)
    (_hrel : Step.Released L X g)
    {d : Mma.D} (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hsite : d.site = .waitDealloc) : Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hg : g < L.threads := hp.1
  have ht : Time.regT < stateTime L g (.inr (.mma d)) := by
    simp only [stateTime, Time.mma, hsite, Time.mmaTail, Time.tailTime]
    exact Time.fixed_lt (by decide)
  obtain ⟨before, hstate⟩ := state_of_time hpre hX hI hW hg hσ ht .dealloc
  obtain ⟨hpoll, h0⟩ := hF.poll hg hσ hsite
  refine Sched.pollBlocked_of hpoll hstate (fun hpar => ?_)
  rw [h0] at hpar
  obtain ⟨l, hl, hz⟩ := TmemAlloc.handshake_short hpre hX hW.tmem
    (HsInitProof.hsInit hpre hX hI.cluster hW.tmem hI.init (ctaOf L g)) hstate hpar
  have hb := hpre.block
  have hgr := hpre.grid
  have hcg := cta_lt hg
  have hy : TmemAlloc.lane0 L (pairCta (ctaOf L g)) + l < L.threads := by
    have : pairCta (ctaOf L g) < L.grid := by unfold pairCta; omega
    simp only [TmemAlloc.lane0, Launch.threads, hb] at this ⊢
    nlinarith
  have hcy : ctaOf L (TmemAlloc.lane0 L (pairCta (ctaOf L g)) + l) = pairCta (ctaOf L g) := by
    simp only [TmemAlloc.lane0, ctaOf, hb]
    omega
  have hwy : warpOf L (TmemAlloc.lane0 L (pairCta (ctaOf L g)) + l) = 12 := by
    simp only [TmemAlloc.lane0, warpOf, hb]
    omega
  refine Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg (ne_nil_of_role hσ) hσ hy ?_
    (hF.lag hg hy hcy hwy hσ hsite hz)
  change L.clusterOfCta (ctaOf L _) = L.clusterOfCta (ctaOf L g)
  rw [hcy]
  simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster, pairCta]
  omega

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
