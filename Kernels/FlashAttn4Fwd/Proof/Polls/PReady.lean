-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Polls.Role
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.PReady
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyBlocked

@[expose] public section

/-! # The MMA warp's P-ready polls

A released pending MMA thread at its P-ready poll `pWait k` polls stage `k % 2`'s P-ready object
of its CTA, with the parity of its successful polls of it (`PReadyPollFacts.poll`). The object has
a final state, since the thread is past its register request (`state_of_time`). When
that state's phase has the poll's parity, the phase is the thread's successful polls, and some
producer of the object has made no more arrivals than it (`Score.pReady_blocked`, from the
routes' context and the absence of faulting records in a safe execution). That producer, a
softmax thread of the stage or a correction thread of the pair, lags the thread
(`PReadyPollFacts.lag_soft`, `lag_corr`), so it is a blocker (`Sched.blk_of_lags`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow MBarrier

noncomputable section

/-- An MMA thread's state at a (second) P-ready poll is after the register requests. -/
theorem regT_lt_mmaTime {L : Launch} {g : Nat} {d : Mma.D} {k : Fin 4}
    (hk : d.site = .pWait k ∨ ∃ lead, d.site = .p2Wait k lead) :
    Time.regT < stateTime L g (.inr (.mma d)) := by
  rcases hk with hk | ⟨lead, hk⟩ <;>
  · simp only [stateTime, Time.mma, hk]
    split_ifs <;> simp only [Time.mmaAt, Time.slotTime, Time.base, Time.regT] <;> omega

/-- A thread's CTA is one of the grid's. -/
theorem cta_lt_grid {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) : ctaOf L g < L.grid := by
  have hb := hpre.block
  simp only [ctaOf, Launch.threads] at hg ⊢
  rw [hb] at hg ⊢
  omega

/-- **A released MMA thread at a P-ready poll polls with a blocker when not ready.** -/
theorem pReady_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (hW : WaitInputs L X)
    (hF : PReadyPollFacts L X) (hRC : Score.RouteCtx P L mem0 kernel asms X) {g : Nat}
    (hp : Frame.Pending L X g) (_hrel : Step.Released L X g)
    {d : Mma.D} (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hsite : ∃ k, d.site = .pWait k) : Sched.PollBlocked (timed L) X g := by
  obtain ⟨k, hk⟩ := hsite
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨hw12, hlead, hpoll⟩ := hF.poll hg hσ hk
  have hst : k.val % 2 < 2 := Nat.mod_lt _ (by decide)
  have ht := regT_lt_mmaTime (L := L) (g := g) (.inl hk)
  obtain ⟨before, hb⟩ := state_of_time hpre hX hI hW hg hσ ht (.pReady ⟨k.val % 2, hst⟩)
  refine Sched.pollBlocked_of hpoll hb fun hpar => ?_
  obtain ⟨hph, a, ha⟩ := Score.pReady_blocked hRC hlead hst ⟨hg, rfl, hw12⟩
    (fun _ hr => InitFirst.fault_free (hs.2 X hX) hr) hb (by simpa using hpar)
  obtain ⟨hy, hly, hwy⟩ := Score.pThread_spec hpre hlead (cta_lt_grid hpre hg) hst a
  rw [hph] at ha
  have hl : Lags L X (Score.pThread L (ctaOf L g) (k.val % 2) a) g (.inr (.mma d)) := by
    rcases hwy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hF.lag_soft hg hy hσ hk hly h1 h2 ha
    · exact hF.lag_corr hg hy hσ hk hly h1 h2 ha
  exact Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg (ne_nil_of_role hσ) hσ hy
    (Score.sameCluster_of_pair hpre hy hg (hly.trans hlead.symm)).2.2 hl

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
