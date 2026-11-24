-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsOutput
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Credit

@[expose] public section

/-! # Producer lag at the statistics credit polls (`CreditPollFacts.lag`)

A softmax thread of stage `st` at `statsW k` of item `i` has `(n + 1) i + s` successful polls of
its stage's credit barrier (`Softmax.Counts.stats`), with `s` the slot of its poll: `0`, `1`,
`t + 2` for the trip's poll, and `0` with `i = T` at the tail (`statsW 3`). Its poll is at the
start of band S `st` of slot `s` of item `i`. A correction thread of its CTA with fewer credits
of the stage (`Correction.Counts.credit`: `(n + 1) i' + creditPos`) is in an earlier item, or in
item `i` at a site with fewer than `s` credits of the stage before it (`mul_add_lt`); every such
site is before band S `st` of slot `s` (`corr_credit_lt`): a stage-0 credit of trip `t` is in
slot `t + 1`, a stage-1 credit of trip `t` in band C 0 of slot `t + 1`, the item's last credits
in slot `n`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Progress

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Lag

/-- **A correction state with fewer credits of stage `st` than `(n + 1) i + s`** is before band
S `st` of slot `s` of item `i` (`s ≤ n`; an item of the cluster unless `s = 0`), and not at its
exit. -/
theorem corr_credit_lt {y : Nat} {c : Correction.D} (hinv : Correction.Inv L y c)
    (hn1 : 1 ≤ Work.n L) {st i s : Nat} (hst : st < 2) (hs : s ≤ Work.n L)
    (hiT : i < Correction.items L y ∨ (s = 0 ∧ i ≤ Correction.items L y))
    (hc : c.i < i ∨ c.i = i ∧ Correction.creditPos L st c < s) :
    Time.correction (Work.n L) (Work.T L y) c + 1 < Time.slotTime (Work.n L) i s (Time.bandS st) ∧
      c.site ≠ .exit := by
  have hn : Correction.trips L = Work.n L := rfl
  obtain ⟨site, ci, ct, aw, a⟩ := c
  have htrip := hinv.trip
  have htail := hinv.tail
  simp only at htrip htail hc ⊢
  rw [hn] at htrip
  have hitem := hinv.item
  simp only at hitem
  by_cases hI : site.inItem = false
  · rcases site with _ | _ | st' | ⟨st', gen⟩ | a | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j⟩ |
      st' | ⟨st', fin⟩ | st' | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j, hh, el⟩ | st' | st' | _ |
      _ | _ <;> simp only [Correction.Site.inItem, Bool.true_eq_false] at hI
    any_goals (rcases Store.fin2_cases st' with rfl | rfl)
    all_goals first
      | (simp [Correction.Site.inItem] at htail
         simp only [Correction.creditPos] at hc
         omega)
      | (refine ⟨lt_of_lt_of_le ?_ (fixed_le_slotTime le_rfl), ?_⟩ <;>
         simp [Time.correction, Time.base, Time.regT, Time.bar0T, Time.freeT])
  have hci := hitem (by simpa using hI)
  rcases (show st = 0 ∨ st = 1 by omega) with rfl | rfl
  all_goals
    rcases site with _ | _ | st' | ⟨st', gen⟩ | a | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j⟩ |
      st' | ⟨st', fin⟩ | st' | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j, hh, el⟩ | st' | st' | _ |
      _ | _
  all_goals simp only [Correction.Site.inItem, Bool.true_eq_false, not_true_eq_false] at hI
  all_goals (try rcases Store.fin2_cases st' with rfl | rfl)
  all_goals (try cases gen)
  all_goals (try cases fin)
  all_goals (try rcases fin6_cases a with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals (try have := j.isLt)
  all_goals (try have := hh.isLt)
  all_goals (try have := el.isLt)
  all_goals
    refine ⟨?_, by simp⟩
    simp only [Correction.Site.inTrip, Correction.creditPos, Time.correction, Fin.val_zero,
      Fin.val_one, Fin.isValue, Bool.false_eq_true, ↓reduceIte, forall_const, hn,
      Nat.one_ne_zero] at htrip hc ⊢
    refine slotTime_lt ?_ ?_ ?_ <;>
      (try simp only [Time.bandC, Time.bandS, Time.span]) <;> omega

end Lag

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

open Lag in
/-- **The field `CreditPollFacts.lag`**. -/
theorem CreditPollFacts_lag :
    ∀ {g y : Nat} {d : Softmax.D}, g < L.threads → y < L.threads →
    ctaOf L y = ctaOf L g → 8 ≤ warpOf L y → warpOf L y < 12 →
    St L X g (X.tr g).length = some (some (.inr (.softmax d))) → (∃ k, d.site = .statsW k) →
    arrivals (statsBar L (ctaOf L g) (warpOf L g / 4)) (X.tr y) + 1 ≤
      okPolls (statsBar L (ctaOf L g) (warpOf L g / 4)) (X.tr g) →
      Lags L X y g (.inr (.softmax d)) := by
  intro g y d hg hy hcta hw1 hw2 hσ hk hle hub
  obtain ⟨hJ, hinv⟩ := end_state hpre hX ht hub hg hσ
  change Softmax.Counts L g d (X.tr g) at hJ
  change Softmax.Inv L g d at hinv
  have hst : warpOf L g / 4 < 2 := by have := hinv.warp; omega
  have hp := hJ.stats
  have hloc : Softmax.ownLoc L g (240 + 8 * Softmax.stOf L g) =
      statsBar L (ctaOf L g) (warpOf L g / 4) := by
    simp [Softmax.ownLoc, statsBar, Softmax.sb]
  rw [hloc] at hp
  have hT := T_eq_of_cta hcta
  have hn1 := n_pos hpre
  have hn : Softmax.trips L = Work.n L := rfl
  -- the waiter's item `i` and slot `s`: `(n + 1) i + s` successful polls, its poll at band S of
  -- slot `s` of item `i`
  obtain ⟨i, s, hs, hiT, hpoll, htime⟩ : ∃ i s, s ≤ Work.n L ∧
      (i < Work.T L g ∨ (s = 0 ∧ i ≤ Work.T L g)) ∧
      okPolls (statsBar L (ctaOf L g) (warpOf L g / 4)) (X.tr g) = (Work.n L + 1) * i + s ∧
      stateTime L g (.inr (.softmax d)) =
        Time.slotTime (Work.n L) i s (Time.bandS (warpOf L g / 4)) := by
    obtain ⟨k, hks⟩ := hk
    obtain ⟨site, i, t⟩ := d
    simp only at hks
    subst hks
    rw [hn] at hp
    have hitem := hinv.item
    have htail := hinv.tail
    have htrip := hinv.trip
    rw [hn] at htrip
    simp only [Softmax.Site.inItem, Softmax.Site.inTrip] at hitem htrip hp
    rcases Softmax.fin4_cases k with rfl | rfl | rfl | rfl
    · refine ⟨i, 0, Nat.zero_le _, .inl (hitem rfl), ?_, rfl⟩
      rw [hp]; simp only [Softmax.statsPos, ↓reduceIte]
    · refine ⟨i, 1, hn1, .inl (hitem rfl), ?_, rfl⟩
      rw [hp]; simp only [Softmax.statsPos, Softmax.Site.tile0, ↓reduceIte]
    · refine ⟨i, t + 2, by have := htrip rfl; omega, .inl (hitem rfl), ?_, rfl⟩
      rw [hp]; simp only [Softmax.statsPos, Softmax.Site.tile0, Bool.false_eq_true, ↓reduceIte]
      omega
    · obtain ⟨hi, -⟩ := htail (.inl rfl)
      refine ⟨i, 0, Nat.zero_le _, .inr ⟨rfl, hi.le⟩, ?_, ?_⟩
      · rw [hp]; simp only [Softmax.tailPos, Bool.false_eq_true, ↓reduceIte]
      · simp only at hi
        subst hi
        rfl
  have hW : Time.base + 2 ≤ stateTime L g (.inr (.softmax d)) := by
    rw [htime]; exact le_slotTime_of (by simp only [Time.bandS, Time.base]; omega)
  refine lags_corr hpre hX ht hub hy ⟨hw1, hw2⟩
    (arrivesOn (statsBar L (ctaOf L g) (warpOf L g / 4))) ((Work.n L + 1) * i + s)
    (stateTime L g (.inr (.softmax d)) - 2) (by omega) (fun c es _ hJc hinvc hcnt => ?_) ?_
    (by omega)
  · have h := hJc.credit (warpOf L g / 4) hst
    have hl : Correction.ownLoc L y (240 + 8 * (warpOf L g / 4)) =
        statsBar L (ctaOf L g) (warpOf L g / 4) := by
      simp [Correction.ownLoc, statsBar, hcta, Correction.sb]
    rw [hl] at h
    change (es.countP (arrivesOn _)) = _ at h
    have hlt : (Work.n L + 1) * c.i + Correction.creditPos L (warpOf L g / 4) c <
        (Work.n L + 1) * i + s := by
      have hn : Correction.trips L = Work.n L := rfl
      rw [hn] at h; rw [← h]; exact hcnt
    obtain ⟨h1, h2⟩ := corr_credit_lt hinvc hn1 hst hs
      (by rw [Correction.items_eq, hT]; exact hiT) (mul_add_lt (by omega) hlt)
    rw [htime]
    exact ⟨by omega, h2⟩
  · change arrivals _ _ + 1 ≤ _ at hle
    unfold arrivals at hle
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof
