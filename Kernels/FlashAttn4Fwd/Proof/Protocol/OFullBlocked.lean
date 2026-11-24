-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.SFullBlocked

@[expose] public section

/-! # Who blocks a correction thread at its O-full wait

Stage `st`'s O-full object of CTA `c` (count 1) is completed by the notifications of the commits
of the committing lane of warp 12 of `c`'s pair leader, multicast over the pair, and polled by
the correction threads of `c` with the parity of their earlier successful polls. It is an object
of a family completed by commits alone (`Score.full_blocked`), with its premises from
`OFullFacts`, `OFullInit` and `OFullReach` (the context of the routes, `RouteCtx`):
`oFull_blocked`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof MBarrier

noncomputable section

namespace OAcc
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **Who blocks a correction thread at its O-full wait**: when stage `st`'s O-full object of
its CTA ends in a phase of the parity of the thread's successful polls of it, the phase is at
most those polls, and the committing lane of warp 12 of the pair leader made no more commits to
the stage's O-full object of its own CTA than the phase number, or some commit's notification is
undelivered. -/
theorem oFull_blocked (H : RouteCtx P L mem0 K A X) (htc : TcFacts L X) {h st : Nat}
    (hh : h < L.threads) (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12) (hst : st < 2)
    (hff : ∀ r ∈ X.objects (oFullBar L (ctaOf L h) st), r.fault = none) {before : State}
    (hs : stateBefore (X.objects (oFullBar L (ctaOf L h) st))
      (X.objects (oFullBar L (ctaOf L h) st)).length = some before)
    (hpar : before.phase % 2 = okPolls (oFullBar L (ctaOf L h) st) (X.tr h) % 2) :
    before.phase ≤ okPolls (oFullBar L (ctaOf L h) st) (X.tr h) ∧
      ∃ y, y < L.threads ∧ warpOf L y = 12 ∧ ctaOf L y = leadCta (ctaOf L h) ∧
        SelfElected L X y ∧
        ((X.tr y).countP (commitsTo (oFullBar L (ctaOf L y) st)) ≤ before.phase ∨
          ¬ ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' →
            rank ∈ X.tcNotified i) := by
  have hc : ctaOf L h < L.grid := by
    unfold ctaOf; unfold Launch.threads at hh; rw [H.pre.block] at hh ⊢; omega
  exact full_blocked H.pre H.cons H.tm htc H.efull (fun _ _ _ => rfl) hc (H.oinit _ _ hst)
    (H.ofa.o_arrive hst) (H.ofa.o_tensor hst)
    (fun he => (H.ofa.o_poll (event_thread_lt H.cons he) hst he).2.2.2.1)
    (fun hg he ht => H.ofa.o_commit hg hst he ht)
    (fun y rank hrec j hj => oFullReach H h st hh h8 h12 hst y rank hrec j hj) hff hs hpar

end OAcc

end
end PTX.Kernels.FlashAttn4Fwd.Proof
