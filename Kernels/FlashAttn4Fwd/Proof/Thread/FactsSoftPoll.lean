-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftBarAgree

@[expose] public section

/-! # The softmax part of `Cross.PollAgree`

Two lanes of a softmax warp polling at one position poll the same site (`Softmax.pc_poll`):
its barrier is the warp's stage's credit or S-full barrier of its CTA. Their rounds there are
the site's round formula of their states (`Counts.rounds`), which fixes the item (and the loop
trip, by `tile_inj`); so their successful polls of the barrier, and the parities, agree. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two lanes of a warp have one item count. -/
theorem soft_items_warp {g h : Nat} (hs : SameWarp L g h) :
    Softmax.items L g = Softmax.items L h := by
  obtain ⟨⟨-, -, hc⟩, -⟩ := hs
  simp only [Softmax.items, Work.T, Work.cid, clusterOf, ctaOf]
  rw [hc]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **The softmax part of `Cross.PollAgree`**: two lanes of a softmax warp polling at one
position in one round poll one barrier with one parity. -/
theorem Cross.PollAgree_soft {g h k k' pc p p' : Nat} {m m' : Loc} {ok ok' acq acq' : Bool}
    {sc sc' : MbarScope} (hw : warpOf L g < 8) (hs : SameWarp L g h)
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hr : pollRound pc ((X.tr g).take k) = pollRound pc ((X.tr h).take k')) :
    m = m' ∧ p % 2 = p' % 2 := by
  have hww : warpOf L g = warpOf L h := hs.2
  have hw' : warpOf L h < 8 := by omega
  have hcta : ctaOf L g = ctaOf L h := hs.1.2.2
  have hst : Softmax.stOf L g = Softmax.stOf L h := by simp only [Softmax.stOf]; rw [hww]
  have hT := soft_trips_pos hpre
  obtain ⟨d, -, hc, hi, hpc, hsd⟩ := soft_wait hpre hX ht hw he
  obtain ⟨d', -, hc', hi', hpc', hsd'⟩ := soft_wait hpre hX ht hw' he'
  have hpoll' : d'.site.isPoll = true := by
    rcases hsd' with ⟨w, h1, -⟩ | ⟨lp, h1, -⟩ <;> rw [h1] <;> rfl
  have hsite : d.site = d'.site := Softmax.pc_poll _ _ hpoll' (hpc.trans hpc'.symm)
  have r1 := hc.rounds d'.site hpoll'
  have r2 := hc'.rounds d'.site hpoll'
  rw [← hsite, hpc] at r1
  rw [hpc'] at r2
  unfold pollRound at hr
  rw [r1, r2] at hr
  have hI := soft_items_warp hs
  have hs1 := hc.stats
  have hs2 := hc'.stats
  have hS1 := hc.score
  have hS2 := hc'.score
  have ht01 := hi.tile0
  have ht02 := hi'.tile0
  have htr1 := hi.trip
  have htr2 := hi'.trip
  have htl1 := hi.tail
  have htl2 := hi'.tail
  have hown : ∀ off, Softmax.ownLoc L g off = Softmax.ownLoc L h off := by
    intro off; simp only [Softmax.ownLoc, hcta]
  obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
  obtain ⟨site', ii', tt', ww', mm', ll'⟩ := d'
  simp only at hsite hr hs1 hs2 hS1 hS2 ht01 ht02 htr1 htr2 htl1 htl2 hsd hsd'
  subst hsite
  rcases hsd with ⟨w, hw1, rfl, hp⟩ | ⟨lp, hw1, rfl, hp⟩ <;>
    rcases hsd' with ⟨w', hw2, rfl, hp'⟩ | ⟨lp', hw2, rfl, hp'⟩ <;>
    subst hw1 <;> simp only [Softmax.Site.statsW.injEq, Softmax.Site.sW.injEq,
      reduceCtorEq] at hw2
  · subst hw2
    rw [hst, hown] at hp hs1 ⊢
    refine ⟨rfl, ?_⟩
    rw [hp, hp', hs1, hs2]
    rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
    · simp [Softmax.roundOf, Softmax.statsPos, Softmax.Site.inItem] at hr ⊢
      rw [hr]
    · simp [Softmax.roundOf, Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0] at hr ⊢
      rw [hr]
    · have a1 := htr1 rfl
      have a2 := htr2 rfl
      simp [Softmax.roundOf, Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0,
        Softmax.Site.inTrip] at hr ⊢
      obtain ⟨e1, e2⟩ := tile_inj (n := Softmax.trips L - 1) (i := ii) (i' := ii') (T := tt)
        (T' := tt') (by omega) (by omega) hr
      rw [e1, e2]
    · obtain ⟨e1, -⟩ := htl1 (.inl rfl)
      obtain ⟨e2, -⟩ := htl2 (.inl rfl)
      simp [Softmax.tailPos, Softmax.Site.inItem]
      rw [e1, e2, hI]
  · subst hw2
    rw [hst, hown] at hp hS1 ⊢
    refine ⟨rfl, ?_⟩
    rw [hp, hp', hS1, hS2]
    cases lp
    · simp [Softmax.roundOf, Softmax.sPos, Softmax.Site.tile0Ld, Softmax.Site.inTrip] at hr ⊢
      rw [hr]
    · have a1 := htr1 rfl
      have a2 := htr2 rfl
      simp [Softmax.roundOf, Softmax.sPos, Softmax.Site.inTrip, Softmax.Site.afterS1] at hr ⊢
      obtain ⟨e1, e2⟩ := tile_inj (n := Softmax.trips L - 1) (i := ii) (i' := ii') (T := tt)
        (T' := tt') (by omega) (by omega) hr
      rw [e1, e2]

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
