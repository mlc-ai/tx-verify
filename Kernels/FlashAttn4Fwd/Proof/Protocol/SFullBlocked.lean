-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReach
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Lemmas.Protocol.NotifyBlocker
public import Lemmas.Flow.ElectActor

@[expose] public section

/-! # Who blocks a softmax thread at its S-full wait

Stage `st`'s S-full object of CTA `c` (count 1) is completed by the notifications of the commits
of one lane of warp 12 of `c`'s pair leader, multicast over the pair, and polled by the softmax
threads of stage `st` of `c` with the parity of their earlier successful polls.

* **The committing lane** (`selfElected_lane`): warp 12 of a launched CTA has a lane `y` every
  election of which returned its own lane, and every lane of the warp whose full-mask election
  returned its own lane is `y`. If some lane of the warp made an election, `y` is the lane of its
  leader (all elections of a warp with one mask return one leader, `ElectOk`); otherwise any lane
  is such a lane, and no lane of the warp made an election.
* **A commit object blocker** (`full_blocked`): an object of a family completed by commits alone
  (the S-full and O-full objects), each commit the elected lane's of warp 12 of the pair leader
  naming the stage's object of its own CTA (`TcFacts.commit_spec`: mask 3 over the pair, so each
  such commit targets the object), is a commit object of that lane
  (`MbarRing.Notify.Obj.of_commits`). With the enabling paths of its reuse as a thread `h` polls
  it and fault-free records, when its final phase has the parity of `h`'s successful polls, the
  phase is at most those polls, and the lane made no more commits to the stage's object of its
  own CTA than the phase number, or some commit's notification is undelivered
  (`MbarRing.Notify.Obj.blocker`).
* **The S-full objects** (`sFull_blocked`): the premises from `SFullFacts`, `SFullInit` and
  `SFullReach` (the context of the routes, `RouteCtx`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof MBarrier

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **The committing lane of warp 12 of a launched CTA**: a lane every election of which returned
its own lane, which is every lane of the warp whose full-mask election returned its own lane. -/
theorem selfElected_lane (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (hfull : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l → mask = fullMask)
    {c : Nat} (hc : c < L.grid) :
    ∃ y, y < L.threads ∧ warpOf L y = 12 ∧ ctaOf L y = c ∧ SelfElected L X y ∧
      ∀ g k, g < L.threads → warpOf L g = 12 → ctaOf L g = c → LeadAt L X g k → g = y := by
  have hb := hpre.block
  by_cases hE : ∃ (e : EvId) (pc mask inst l : Nat), X.Elect e pc mask inst l ∧
      warpOf L e.1 = 12 ∧ ctaOf L e.1 = c
  · -- the warp's elections all return one leader lane `l` (`ElectOk`, full masks)
    obtain ⟨e, pc, mask, inst, l, he, hw, hce⟩ := hE
    obtain ⟨he1, -, hl, -⟩ := hX.elect.1 e pc mask inst l he
    have hsw : ∀ g, g < L.threads → warpOf L g = 12 → ctaOf L g = c → SameWarp L e.1 g :=
      fun g hg hwg hcg => ⟨⟨he1, hg, by unfold ctaOf at hce hcg; omega⟩,
        by unfold warpOf at hw hwg; omega⟩
    have hy : c * L.block + 384 + l < L.threads := by
      unfold Launch.threads; rw [hb]; omega
    have hwy : warpOf L (c * L.block + 384 + l) = 12 := by unfold warpOf; rw [hb]; omega
    have hcy : ctaOf L (c * L.block + 384 + l) = c := by unfold ctaOf; rw [hb]; omega
    have hly : laneOf L (c * L.block + 384 + l) = l := by unfold laneOf; rw [hb]; omega
    have hm := hfull he
    subst hm
    refine ⟨_, hy, hwy, hcy, fun j' pc' mask' inst' l' he' => ?_,
      fun g k hg hwg hcg hlead => ?_⟩
    · rw [hfull he'] at he'
      rw [← hX.elect.2.2 _ _ _ _ _ _ _ _ _ he he' (hsw _ hy hwy hcy), hly]
    · obtain ⟨j0, -, pc0, inst0, hg0⟩ := hlead
      have hll := hX.elect.2.2 _ _ _ _ _ _ _ _ _ he hg0 (hsw g hg hwg hcg)
      have hlg : laneOf L g = l := hll.symm
      unfold laneOf at hlg
      unfold warpOf at hwg
      unfold ctaOf at hcg
      rw [hb] at hlg hwg hcg ⊢
      omega
  · push Not at hE
    have hy : c * L.block + 384 < L.threads := by
      unfold Launch.threads; rw [hb]; omega
    have hwy : warpOf L (c * L.block + 384) = 12 := by unfold warpOf; rw [hb]; omega
    have hcy : ctaOf L (c * L.block + 384) = c := by unfold ctaOf; rw [hb]; omega
    refine ⟨_, hy, hwy, hcy, fun j pc mask inst l he => absurd hcy (hE _ pc mask inst l he hwy),
      fun g k _ hwg hcg hlead => ?_⟩
    obtain ⟨j0, -, pc0, inst0, hg0⟩ := hlead
    exact absurd hcg (hE (g, j0) _ _ _ _ hg0 hwg)

/-- **Who blocks a thread at a poll of an object completed by commits.** -/
theorem full_blocked (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (htm : TmemFacts L X)
    (htc : TcFacts L X)
    (hfull : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l → mask = fullMask)
    {bar : Nat → Nat → Loc} (hbar : ∀ c c' st, bar c st = ⟨.shared, c, (bar c' st).addr⟩)
    {c st h : Nat} (hc : c < L.grid) (hinit : PairTmaRing.InitFirst X (bar c st) 1)
    (harr : ∀ {g i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
      X.get (g, i) ≠ some ⟨pc, .arrive (bar c st) tx cnt rel sc⟩)
    (hten : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
      X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ bar c st)
    (hpoll : ∀ {g k pc p : Nat} {acq : Bool} {sc : MbarScope},
      X.get (g, k) = some ⟨pc, .wait (bar c st) p true acq sc⟩ →
        p % 2 = okPolls (bar c st) ((X.tr g).take k) % 2)
    (hcom : ∀ {g k pc : Nat} {sp : TcCommit.Spec} {r : Fin 16}, g < L.threads →
      X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (bar c st) →
        warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
          sp.mbar = bar (ctaOf L g) st)
    (hR : ∀ (y : EvId) (rank : Fin 16), (∃ r ∈ X.objects (bar c st),
        r.id = .async y (.tcNotify rank) ∧ r.fault = none) →
      ∀ j < ((X.tr y.1).take y.2).countP (commitsTo (bar (ctaOf L y.1) st)),
        Relation.TransGen (DepStep L K X)
          (.thread (h, MbarRing.Poll.nth X (bar c st) h j), true)
          (.async y (.tcNotify rank), false))
    (hff : ∀ r ∈ X.objects (bar c st), r.fault = none) {before : State}
    (hs : stateBefore (X.objects (bar c st)) (X.objects (bar c st)).length = some before)
    (hpar : before.phase % 2 = okPolls (bar c st) (X.tr h) % 2) :
    before.phase ≤ okPolls (bar c st) (X.tr h) ∧ ∃ y, y < L.threads ∧ warpOf L y = 12 ∧
      ctaOf L y = leadCta c ∧ SelfElected L X y ∧
      ((X.tr y).countP (commitsTo (bar (ctaOf L y) st)) ≤ before.phase ∨
        ¬ ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' →
          rank ∈ X.tcNotified i) := by
  have hlc : leadCta c < L.grid := by unfold leadCta; omega
  obtain ⟨y, hy, hwy, hcy, hself, huniq⟩ := selfElected_lane hpre hX hfull hlc
  have hcom' : ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {r : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp r = some (bar c st) →
        i.1 = y ∧ sp.mbar = bar (ctaOf L y) st := by
    intro i pc sp r he ht
    obtain ⟨g, k⟩ := i
    have hg := event_thread_lt hX he
    obtain ⟨hw, hl, hlead, hm⟩ := hcom hg he ht
    have hgy := huniq g k hg hw hl.symm hlead
    subst hgy
    exact ⟨rfl, hm⟩
  have O : MbarRing.Notify.Obj X (bar c st) y (bar (ctaOf L y) st) 0 :=
    MbarRing.Notify.Obj.of_commits hX hinit harr hten (fun he => (htm.no_bulk he).elim)
      (fun he => (htm.no_arriveOn he).elim) htm.no_clc htm.no_inval hcom'
      (fun he => by simpa using hpoll he) (Nat.zero_le _)
  have hRe := MbarRing.Notify.Reach.of_records (A := A) O (h := h)
    (fun i rank hrec j hj => hR (y, i) rank hrec j hj)
  have htgt : ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = bar (ctaOf L y) st →
        ∃ rank, TcCommit.target sp rank = some (bar c st) := by
    intro i pc sp he hm
    obtain ⟨-, -, b, -, rfl⟩ := htc.commit_spec hy he
    have hc2 : c = ctaOf L y + c % 2 := by unfold leadCta at hcy; omega
    have hr : c % 2 < 2 ∧ (3 : BitVec 16).toNat / 2 ^ (c % 2) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one c with h0 | h0 <;> rw [h0] <;> decide
    refine ⟨⟨c % 2, by omega⟩, ?_⟩
    simp only at hm
    simp only [TcCommit.target]
    rw [ite_eq_left hr, hm, hbar c (ctaOf L y) st, ← hc2]
  obtain ⟨hle, hb⟩ := O.blocker hX hRe hff htgt hs (by simpa using hpar) (Nat.zero_le _)
  exact ⟨by simpa using hle, y, hy, hwy, hcy, hself, hb⟩

/-- **Who blocks a softmax thread at its S-full wait**: when its stage's S-full object of its
CTA ends in a phase of the parity of the thread's successful polls of it, the phase is at most
those polls, and the committing lane of warp 12 of the pair leader made no more commits to the
stage's S-full object of its own CTA than the phase number, or some commit's notification is
undelivered. -/
theorem sFull_blocked (H : RouteCtx P L mem0 K A X) (htc : TcFacts L X) {h : Nat}
    (hh : h < L.threads) (hw : warpOf L h < 8)
    (hff : ∀ r ∈ X.objects (sFullBar L (ctaOf L h) (warpOf L h / 4)), r.fault = none)
    {before : State}
    (hs : stateBefore (X.objects (sFullBar L (ctaOf L h) (warpOf L h / 4)))
      (X.objects (sFullBar L (ctaOf L h) (warpOf L h / 4))).length = some before)
    (hpar : before.phase % 2 =
      okPolls (sFullBar L (ctaOf L h) (warpOf L h / 4)) (X.tr h) % 2) :
    before.phase ≤ okPolls (sFullBar L (ctaOf L h) (warpOf L h / 4)) (X.tr h) ∧
      ∃ y, y < L.threads ∧ warpOf L y = 12 ∧ ctaOf L y = leadCta (ctaOf L h) ∧
        SelfElected L X y ∧
        ((X.tr y).countP (commitsTo (sFullBar L (ctaOf L y) (warpOf L h / 4))) ≤
            before.phase ∨
          ¬ ∀ i s rank m', X.Commit i s → TcCommit.target s rank = some m' →
            rank ∈ X.tcNotified i) := by
  have hst : warpOf L h / 4 < 2 := by omega
  have hc : ctaOf L h < L.grid := by
    unfold ctaOf; unfold Launch.threads at hh; rw [H.pre.block] at hh ⊢; omega
  exact full_blocked H.pre H.cons H.tm htc H.efull (fun _ _ _ => rfl) hc (H.sinit _ _ hst)
    (H.sf.s_arrive hst) (H.sf.s_tensor hst)
    (fun he => (H.sf.s_poll (event_thread_lt H.cons he) hst he).2.2.2.1)
    (fun hg he ht => H.sf.s_commit hg hst he ht)
    (fun y rank hrec j hj => sFullReach H h hh hw y rank hrec j hj) hff hs hpar

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
