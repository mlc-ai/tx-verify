-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.LifetimeReach
public import Kernels.FlashAttn4Fwd.Proof.Interface.Async
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A thread's uses of the other CTA of its pair finish before that CTA exits

The premise `PeerThreadFinished` of `Safety.no_sharedLifetimeUnsafe`
(`peerThreadFinished`): a thread instruction's use of a CTA other than its own (`SharedUse`)
completes before an exit of that CTA once it exited. A thread accesses only its own CTA's shared
memory (`AsyncFacts.access_own`), initializes and polls only its own CTA's barriers
(`ClusterFacts.init_site`, `ExitFacts.wait_own`), and its other uses are of the other CTA of its
pair (`AsyncFacts.mbar_pair`, the commit's CTA group):

* the handshake arrival of a lane of warp 12 on the other CTA's barrier happens before the exit of
  lane 0 of that CTA's warp 12 (`hs_baseCausality`);
* every other use (a remote arrival of a softmax, correction or MMA thread, the leader's commit
  issue) comes before its thread's second barrier-2 event (`ExitFacts.peer_bar2`), so it reaches
  an exit of the other CTA (`reach_bar2`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier TmemAlloc

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event that is not on barrier 2 adds nothing to the count of barrier-2 events. -/
theorem barOrd_succ {g j : Nat} {ev : Event} (he : X.get (g, j) = some ev)
    (hn : Execution.isBarId 2 ev = false) : barOrd X g (j + 1) 2 = barOrd X g j 2 := by
  unfold barOrd
  rw [Stats.countP_take_succ (show (X.tr g)[j]? = some ev from he), hn]
  rfl

/-- **The use of another CTA by a thread instruction other than a handshake arrival** reaches an
exit of that CTA. -/
theorem peer_reach (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) (hs : StatsFacts L X) (hx : ExitFacts P L X)
    (hi : ∀ c, HsInit L X c) {c g j : Nat} {ev : Event} (hex : CtaExited L X c)
    (hcg : c / 2 = ctaOf L g / 2) (he : X.get (g, j) = some ev) (hp : PeerEvent L g ev) :
    ReachesExit L X c (g, j) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, hord⟩ := hx.peer_bar2 hg he hp
  have hnb : Execution.isBarId 2 ev = false := by
    rcases hp with ⟨m, tx, cnt, rel, sc, hk, -⟩ | ⟨sp, hk⟩ <;>
      · obtain ⟨pc, k⟩ := ev
        simp only at hk
        subst hk
        rfl
  exact reach_bar2 hpre hX htm hs hx hi hex (pair_lt hpre (cta_lt hg) hcg) hg hcg.symm hw
    (by rw [barOrd_succ he hnb]; exact hord)

/-- **The handshake arrival** of a lane of warp 12 on CTA `c`'s barrier happens before an exit of
`c` once `c` exited. -/
theorem hs_reach (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) (hx : ExitFacts P L X) (hi : ∀ c, HsInit L X c) {c g j pc tx cnt : Nat}
    {rel : Bool} {sc : MbarScope} (hex : CtaExited L X c)
    (he : X.get (g, j) = some ⟨pc, .arrive (hsLoc L c) tx cnt rel sc⟩) :
    ReachesExit L X c (g, j) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, hcta, -, -, huniq⟩ := htm.hs_arrive hg he rfl
  have hc : c < L.grid := by
    rw [hcta]
    exact pairCta_lt hpre (cta_lt hg)
  obtain ⟨k0, pc0, hk0⟩ := exit_of_exited hex (lane0_lt hpre hc) (cta_lane0 hpre c)
  obtain ⟨hgl, hl⟩ := lane_of_warp hpre hw
  obtain ⟨a, pca, tx', cnt', ha, hab⟩ := hs_baseCausality hpre hX htm hx (hi c) hk0 hl
  have hpg : lane0 L (pairCta c) + g % 32 = g := by
    rw [hcta, pairCta_pairCta]
    exact hgl.symm
  rw [hpg] at ha hab
  have := huniq a pca tx' cnt' true .cluster ha
  subst this
  exact ⟨(lane0 L c, k0), ⟨lane0_lt hpre hc, cta_lane0 hpre c, pc0, hk0⟩, hab⟩

/-- **PeerThreadFinished**: a thread instruction's use of another CTA completes before an exit of
that CTA once it exited. -/
theorem peerThreadFinished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) (hs : StatsFacts L X) (hcf : ClusterFacts L X)
    (ha : AsyncFacts P L X) (hx : ExitFacts P L X) (hi : ∀ c, HsInit L X c) :
    ∀ (i : EvId) (c : Nat), SharedUse L X (.thread i) c → c ≠ ctaOf L i.1 → CtaExited L X c →
      SharedFinished L kernel asms X (.thread i) c := by
  intro i c huse hne hex
  obtain ⟨g, j⟩ := i
  rcases huse with ⟨-, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i', s, hi', ⟨pc, he⟩, hgrp⟩ | ⟨_, _, _, _, _, _, h, -⟩ | ⟨_, _, _, h, -⟩ |
      ⟨_, _, h, -⟩
  · exact absurd (hcta ▸ ha.access_own hint hsp) hne
  · have hsrc := objectAction_source
      (r := { id := .thread (g, j), action := act, reply := { state := none }, fault := none })
      hact
    cases hsrc with
    | @init g' j' pc n hid he _ =>
      simp only [Ref.thread.injEq, Prod.mk.injEq] at hid
      obtain ⟨rfl, rfl⟩ := hid
      obtain ⟨b, hm, -⟩ := hcf.init_site (Frame.lt_of_get hX he) he
      exact absurd (congrArg Loc.cta hm) hne
    | inval _ he _ => exact (htm.no_inval he).elim
    | @arrive g' j' pc tx n rel sc hid he _ =>
      simp only [Ref.thread.injEq, Prod.mk.injEq] at hid
      obtain ⟨rfl, rfl⟩ := hid
      by_cases hhs : (⟨.shared, c, addr⟩ : Loc) = FBar.loc L c .dealloc
      · rw [hhs] at he
        exact SharedFinished.of_baseCausality he (hs_reach hpre hX htm hx hi hex he)
      · obtain ⟨b, c', hm, hcp⟩ := ha.mbar_pair (e := (g, j)) (.inl ⟨tx, n, rel, sc, pc, he⟩)
        have hcg : c / 2 = ctaOf L g / 2 := by
          have := congrArg Loc.cta hm
          simp only [FBar.loc] at this
          rw [this]
          exact hcp
        exact SharedFinished.of_baseCausality he (peer_reach hpre hX htm hs hx hi hex hcg he
          (.inl ⟨_, tx, n, rel, sc, rfl, hne, hhs⟩))
    | @wait g' j' pc q ok acq sc hid he _ =>
      simp only [Ref.thread.injEq, Prod.mk.injEq] at hid
      obtain ⟨rfl, rfl⟩ := hid
      exact absurd (hx.wait_own (Frame.lt_of_get hX he) he) hne
    | tensor hid _ _ _ => cases hid
    | increment _ he _ => exact (htm.no_arriveOn he).elim
    | arriveOn hid _ _ _ _ => cases hid
    | bulk hid _ _ _ _ => cases hid
    | commit hid _ _ _ => cases hid
    | clc hid _ _ _ _ => cases hid
  · simp only [Ref.thread.injEq] at hi'
    subst hi'
    obtain ⟨⟨-, -, h3⟩, -⟩ := (sameCtaGroup_iff _ _ _ _).mp hgrp
    have hcg : c / 2 = ctaOf L g / 2 := by
      simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster] at h3
      exact h3.symm
    exact SharedFinished.of_baseCausality he
        (peer_reach hpre hX htm hs hx hi hex hcg he (.inr ⟨s, rfl⟩))
  all_goals cases h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
