-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Progress.PollTime
public import Kernels.FlashAttn4Fwd.Proof.Progress.Collective
public import Kernels.FlashAttn4Fwd.Proof.Progress.NextFire
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressAsync
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Loader
public import Kernels.FlashAttn4Fwd.Proof.Protocol.LoaderBlocked
public import Lemmas.Protocol.ElectCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.ElectFull

@[expose] public section

/-! # The loader's empty waits and drain have a blocker

A loader lane at a Q or KV empty wait, or at a poll of its drain, polls its CTA's empty barrier
partnered with `loaderPollBar d` (`LoaderPollFacts.poll`), which has a state (`Rings.ring_state`,
from the lane's event after the start). When the barrier's final phase has the parity the poll
does not find, `Rings.loaderBlocked` leaves three cases:

* the pair's MMA lane made fewer commits to the slot than the lane's successful polls: it is
  self-elected (`Rings.leadOf_selfElected`), so it lags the lane (`LoaderPollFacts.lag`), a
  blocker of the lane's cluster (`Sched.blk_of_lags`);
* a commit has an undelivered target: an open commit obligation;
* the lead loader lane of the CTA issued the copies of one use more than the lane's polls: it
  then made more elections than the lane (`LoaderPollFacts.lane`), but the lanes of a warp make
  equally many full-mask elections (`electCount_le`), so this case does not occur. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- The full barrier of a loader poll site is a ring full barrier. -/
theorem loaderPollBar_isFull {d : Loader.D} (h : loaderKind d.site = .wait) :
    (loaderPollBar d).isFull := by
  rcases d with ⟨site, i, t, s, ph, qp⟩
  cases site <;> simp [loaderKind] at h <;>
    first
    | (rename_i u; cases u <;> rfl)
    | rfl

/-- **The loader's empty waits and drain have a blocker.** -/
theorem loader_pollBlocked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (hmax : Maximal L kernel asms mem0 X) (hI : AsyncInputs P L X) (_hW : WaitInputs L X)
    (hF : LoaderPollFacts L X) {g : Nat} (hp : Frame.Pending L X g)
    (_hrel : Step.Released L X g) {d : Loader.D}
    (hσ : St L X g (X.tr g).length = some (some (.inr (.loader d))))
    (hsite : loaderKind d.site = .wait) : Sched.PollBlocked (timed L) X g := by
  have hX := hmax.1
  have hg : g < L.threads := hp.1
  obtain ⟨hw, hpoll⟩ := hF.poll hg hσ hsite
  have hb := loaderPollBar_isFull hsite
  set b := loaderPollBar d with hbdef
  have hinit := InitFirst.ringInit hpre hX hI.cluster hI.tmem hI.init hI.rings
  have H := Rings.hyp hpre hX hI.rings hI.tmem hinit hb (ctaOf L g / 2)
  obtain ⟨hprod, hempty⟩ := Rings.slot_rank (X := X) (b := b) g
  have hni : MBarrier.NoInval (X.objects (b.partner.loc L (ctaOf L g))) := by
    rw [← hempty]; exact H.empty_noInval _
  obtain ⟨j, ev, he, hk, hub⟩ := hF.started hg hσ hsite
  obtain ⟨before, hstate⟩ := Rings.ring_state hpre hX hI.cluster hI.init hni he hk hub rfl
  refine Sched.pollBlocked_of hpoll hstate fun hpar => ?_
  have hgrid := cta_lt hg
  have hpb : pairBase L g < L.grid := by unfold pairBase; omega
  rcases Rings.loaderBlocked hpre hX hI.rings hI.tmem hinit hI.tc hb hg hstate hpar with
    h | h | h
  · -- the MMA lane lags the lane
    have hy := Rings.leadOf_lt (X := X) hpre (w := 12) (by decide) hpb
    obtain ⟨hcy, hwy⟩ := Rings.leadOf_place (X := X) hpre (cta := pairBase L g) (w := 12)
      (by decide)
    have hne : X.tr g ≠ [] := ne_nil_of_kind hσ (by
      change loaderKind d.site ≠ .warp
      rw [hsite]; decide)
    have ht := wait_base_le L g (d := .inr (.loader d)) hsite
    refine Sched.blk_of_lags hX (Sched.safe_noUb (hs.2 X hX)) hg hne hσ hy ?_
      (hF.lag hg hy hσ hsite hwy hcy
        (Rings.leadOf_selfElected hpre hX (fun he => elect_full hX he) (by decide))
        (by rw [hcy]; exact h))
    change L.clusterOfCta (ctaOf L _) = L.clusterOfCta (ctaOf L g)
    rw [hcy]
    simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster, pairBase]
    omega
  · exact .inl ⟨.commit, .inl rfl, h⟩
  · -- the lead loader lane would have made more elections than the lane
    exfalso
    have hy := Rings.leadOf_lt (X := X) hpre (w := 14) (by decide) hgrid
    obtain ⟨hcy, hwy⟩ := Rings.leadOf_place (X := X) hpre (cta := ctaOf L g) (w := 14)
      (by decide)
    have hsw : SameWarp L g (Rings.leadOf L X (ctaOf L g) 14) :=
      ⟨⟨hg, hy, hcy.symm⟩, by
        change warpOf L g = warpOf L _
        rw [hwy, hw]⟩
    have hlt := hF.lane hg hy hsw hσ hsite h
    have hle := electCount_le hX (fun he => elect_full hX he) (sameWarp_symm hsw)
    omega

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
