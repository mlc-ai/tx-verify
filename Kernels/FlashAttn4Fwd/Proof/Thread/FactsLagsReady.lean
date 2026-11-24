-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsMma
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.PReady
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.P2

@[expose] public section

/-! # Producer lag at the P-ready polls (`PReadyPollFacts.lag_soft`, `lag_corr`,
`P2PollFacts.lag_soft`)

An MMA thread at `pWait k` or `p2Wait k _` of item `i` in trip `t` (the last trip `n - 1` after
the loop) has made `n i + t` successful polls of the polled object (`Mma.Counts.pReady`,
`pReady2`), and polls in band M of slot `t + 1` of item `i` (`mma_ready`).

* A softmax thread of the stage with at most `n i + t` arrivals (`Softmax.Counts.pReady`,
  `pReady2`: `n i' + pPos`, `n i' + p2Pos`) is in an earlier item or, in item `i`, has not made
  its arrival of tile `t` (`tileNo + afterP ≤ t`): it is in band S of a slot at most `t`
  (`soft_ready_lt`).
* A correction thread with at most `n i + t` O-free arrivals of the stage
  (`Correction.Counts.free`: `n i' + freePos`, counting the initial arrival) has not made the
  arrival of trip `t - 1` of item `i` (the end of item `i - 1`, or the initial one, for `t = 0`):
  it is in a slot at most `t` of item `i`, an earlier item, or before the items
  (`corr_free_lt`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Progress

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Lag

/-- **A softmax state that has not made its P-ready arrival (or its elected arrival) of tile
`t` of item `i`** (`t < n`, `i` an item of the cluster) is before band M of slot `t + 1` of item
`i`, and not at its exit. -/
theorem soft_ready_lt {y : Nat} {c : Softmax.D} (hinv : Softmax.Inv L y c) (hn1 : 1 ≤ Work.n L)
    {st i t o : Nat} (hst : st < 2) (ht : t + 1 ≤ Work.n L) (hiT : i < Softmax.items L y)
    (hc : c.i < i ∨ c.i = i ∧ (Softmax.pPos c ≤ t ∨ Softmax.p2Pos c ≤ t)) :
    Time.softmax (Work.n L) (Work.T L y) st c + 1 < Time.slotTime (Work.n L) i (t + 1) o ∧
      c.site ≠ .exit := by
  have hn : Softmax.trips L = Work.n L := rfl
  obtain ⟨site, ci, ct⟩ := c
  have htrip := hinv.trip
  have htail := hinv.tail
  have hlast := hinv.last
  have hitem := hinv.item
  simp only [hn] at htrip htail hlast hitem hc ⊢
  rcases site with _ | _ | w | lp | ⟨lp, cc⟩ | ⟨lp, cc⟩ | _ | j | ⟨lp, cc⟩ | ⟨lp, cc⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin4_cases cc with rfl | rfl | rfl | rfl)
  all_goals (try rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl)
  all_goals (try cases lp)
  all_goals first
    | (simp at htail
       omega)
    | (refine ⟨?_, by simp⟩
       simp only [Softmax.Site.inTrip, Softmax.Site.tile0, Softmax.Site.inItem, Softmax.pPos,
         Softmax.p2Pos, Softmax.tileNo, Softmax.Site.afterP, Softmax.Site.afterP2,
         Time.softmax, Time.softSlot, Bool.false_eq_true, Bool.true_or, Bool.or_true,
         Bool.or_false, decide_true, decide_false, reduceCtorEq, ↓reduceIte,
         forall_const, true_or, or_true, Fin.isValue,
         Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceLT] at htrip hlast hitem hc ⊢
       refine slotTime_lt ?_ ?_ ?_ <;>
         (try simp only [Time.bandS, Time.span]) <;> omega)
    | (refine ⟨lt_of_lt_of_le ?_ (fixed_le_slotTime le_rfl), ?_⟩ <;>
        simp [Time.softmax, Time.base, Time.regT, Time.bar0T])

/-- **A correction state with at most `n i + t` O-free arrivals of stage `st`** (`t < n`, `i` an
item of the cluster) is before band M of slot `t + 1` of item `i`, and not at its exit. -/
theorem corr_free_lt {y : Nat} {c : Correction.D} (hinv : Correction.Inv L y c)
    (hn1 : 1 ≤ Work.n L) {st i t o : Nat} (hst : st < 2) (ht : t + 1 ≤ Work.n L)
    (hiT : i < Correction.items L y)
    (hc : c.i < i ∨ c.i = i ∧ Correction.freePos L st c ≤ t) :
    Time.correction (Work.n L) (Work.T L y) c + 1 < Time.slotTime (Work.n L) i (t + 1) o ∧
      c.site ≠ .exit := by
  have hn : Correction.trips L = Work.n L := rfl
  obtain ⟨site, ci, ct, aw, a⟩ := c
  have htrip := hinv.trip
  have htail := hinv.tail
  simp only at htrip htail hc ⊢
  rw [hn] at htrip
  rcases (show st = 0 ∨ st = 1 by omega) with rfl | rfl
  all_goals
    rcases site with _ | _ | st' | ⟨st', gen⟩ | a | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j⟩ |
      st' | ⟨st', fin⟩ | st' | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j, hh, el⟩ | st' | st' | _ |
      _ | _
  all_goals (try rcases Store.fin2_cases st' with rfl | rfl)
  all_goals (try cases gen)
  all_goals (try cases fin)
  all_goals (try rcases fin6_cases a with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals (try have := j.isLt)
  all_goals (try have := hh.isLt)
  all_goals (try have := el.isLt)
  all_goals first
    | (simp [Correction.Site.inItem] at htail
       omega)
    | (refine ⟨?_, by simp⟩
       simp only [Correction.Site.inTrip, Correction.freePos, Time.correction, Fin.val_zero,
         Fin.val_one, Fin.isValue, Bool.false_eq_true, ↓reduceIte, forall_const, hn,
         Nat.one_ne_zero] at htrip hc ⊢
       refine slotTime_lt ?_ ?_ ?_ <;>
         (try simp only [Time.bandC, Time.span]) <;> omega)
    | (refine ⟨lt_of_lt_of_le ?_ (fixed_le_slotTime le_rfl), ?_⟩ <;>
        simp [Time.correction, Time.base, Time.regT, Time.bar0T, Time.freeT])

/-- **An MMA thread at a P-ready poll** of item `i` in trip `t` has `n i + t` successful polls
of the polled object, `t < n`, `i` is an item of the cluster, and the poll is in band M of slot
`t + 1`. -/
theorem mma_ready (hpre : Pre P L mem0) {g : Nat} {d : Mma.D} {es : List Event}
    (hJ : Mma.Counts L g d es) (hinv : Mma.Inv L g d) {k : Fin 4}
    (hs : d.site = .pWait k ∨ ∃ lead, d.site = .p2Wait k lead) :
    d.t + 1 ≤ Work.n L ∧ d.i < Work.T L g ∧
      (d.site = .pWait k →
        okPolls (Mma.bar L g (.pReady (Mma.stOf k))) es = Work.n L * d.i + d.t) ∧
      (∀ lead, d.site = .p2Wait k lead →
        okPolls (Mma.bar L g (.pReady2 (Mma.stOf k))) es = Work.n L * d.i + d.t) ∧
      Time.mma (Work.n L) (Work.T L g) d =
        Time.slotTime (Work.n L) d.i (d.t + 1) (Time.bandM + Time.mmaOff d.site) := by
  have hn : Mma.trips L = Work.n L := rfl
  have hp := hJ.pReady (Mma.stOf k)
  have hp2 := hJ.pReady2 (Mma.stOf k)
  have htrip := hinv.trip
  have hi := hinv.i
  have hph : d.site.phase = 1 := by rcases hs with h | ⟨_, h⟩ <;> rw [h] <;> rfl
  have hT := mma_time (Work.n L) (Work.T L g) d hph
  obtain ⟨site, i, t, b, pr⟩ := d
  simp only [Mma.cnt, Nat.one_mul, Nat.add_zero, hn] at hp hp2 htrip hi hT ⊢
  unfold Mma.TripOk at htrip
  rw [hn] at htrip
  have hiT := (Work.mma_work_lt hpre).mp (hi (itemSite_of_phase _ hph)).1
  rcases hs with rfl | ⟨lead, rfl⟩
  · refine ⟨?_, hiT, fun _ => ?_, (fun _ h => by cases h), ?_⟩ <;> fin_cases k <;>
      simp [Mma.region, Mma.pA, Mma.Site.inTrip, Mma.Site.after, Mma.Site.loop, Mma.Site.ord,
        Mma.pOrd, Mma.stOf, Time.mmaAt] at htrip hp hT ⊢ <;>
      first | omega | (rw [hT]; congr 1; omega)
  · refine ⟨?_, hiT, (fun h => by cases h), fun _ _ => ?_, ?_⟩ <;> fin_cases k <;>
      simp [Mma.region, Mma.p2A, Mma.Site.inTrip, Mma.Site.after, Mma.Site.loop, Mma.Site.ord,
        Mma.p2Ord, Mma.stOf, Time.mmaAt] at htrip hp2 hT ⊢ <;>
      first | omega | (rw [hT]; congr 1; omega)

end Lag

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- The waiter's facts at a P-ready poll, from its end state: `n i + t` successful polls of the
object, `t < n`, `i < T`, and its time in band M of slot `t + 1` of item `i`. -/
theorem Lag.ready_waiter (hub : ¬ HasUb X) {g : Nat} {d : Mma.D} {k : Fin 4} {b : FBar}
    (hg : g < L.threads) (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hs : d.site = .pWait k ∧ b = .pReady (Mma.stOf k) ∨
      ∃ lead, d.site = .p2Wait k lead ∧ b = .pReady2 (Mma.stOf k)) :
    d.t + 1 ≤ Work.n L ∧ d.i < Work.T L g ∧
      okPolls (b.loc L (ctaOf L g)) (X.tr g) = Work.n L * d.i + d.t ∧
      stateTime L g (.inr (.mma d)) =
        Time.slotTime (Work.n L) d.i (d.t + 1) (Time.bandM + Time.mmaOff d.site) := by
  obtain ⟨hJ, hinv⟩ := Lag.end_state hpre hX ht hub hg hσ
  change Mma.Counts L g d (X.tr g) at hJ
  replace hinv : Mma.Inv L g d := hinv.1
  rcases hs with ⟨hs, rfl⟩ | ⟨lead, hs, rfl⟩
  · obtain ⟨h1, h2, h3, -, h5⟩ := Lag.mma_ready hpre hJ hinv (.inl hs)
    exact ⟨h1, h2, h3 hs, h5⟩
  · obtain ⟨h1, h2, -, h4, h5⟩ := Lag.mma_ready hpre hJ hinv (.inr ⟨lead, hs⟩)
    exact ⟨h1, h2, h4 lead hs, h5⟩

open Lag in
/-- **The field `PReadyPollFacts.lag_soft`**. -/
theorem PReadyPollFacts_lag_soft :
    ∀ {g y : Nat} {d : Mma.D} {k : Fin 4}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .pWait k →
    leadCta (ctaOf L y) = ctaOf L g → warpOf L y < 8 → warpOf L y / 4 = k.val % 2 →
    arrivals (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr y) ≤
      okPolls (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr g) →
      Lags L X y g (.inr (.mma d)) := by
  intro g y d k hg hy hσ hs hlead hw hst hle hub
  obtain ⟨ht1, hiT, hp, hW⟩ :=
    ready_waiter hpre hX ht hub (b := .pReady (Mma.stOf k)) hg hσ (.inl ⟨hs, rfl⟩)
  change okPolls (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr g) = _ at hp
  have hT : Work.T L y = Work.T L g :=
    T_eq_of_pair hpre (by simp only [leadCta] at hlead; omega)
  have hn1 := n_pos hpre
  have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
    rw [hW]; exact le_slotTime_of (by simp only [Time.bandM, Time.base]; omega)
  refine lags_soft hpre hX ht hub hy hw (arrivesOn (pReadyBar L (ctaOf L g) (k.val % 2)))
    (Work.n L * d.i + d.t + 1) (stateTime L g (.inr (.mma d)) - 2) (by omega)
    (fun c es _ hJc hinvc hcnt => ?_) (by change arrivals _ _ < _; omega) (by omega)
  have h := hJc.pReady
  have hl : Softmax.leadLoc L y (144 + 8 * Softmax.stOf L y) =
      pReadyBar L (ctaOf L g) (k.val % 2) := by
    simp only [Softmax.leadLoc, pReadyBar, Softmax.sb, Softmax.stOf, hst]
    simp only [leadCta] at hlead
    congr 1
    omega
  rw [hl] at h
  change es.countP _ = _ at h
  have hn : Softmax.trips L = Work.n L := rfl
  rw [hn] at h
  have hlt := mul_add_lt (m := Work.n L) (a := c.i) (b := d.i) (x := Softmax.pPos c)
    (y := d.t + 1) ht1 (by omega)
  obtain ⟨h1, h2⟩ := soft_ready_lt hinvc hn1 (st := Softmax.stOf L y)
    (o := Time.bandM + Time.mmaOff d.site) (by simp only [Softmax.stOf]; omega) ht1
    (by simp only [Softmax.items]; rw [hT]; exact hiT) (by omega)
  rw [hW]
  exact ⟨by omega, h2⟩

open Lag in
/-- **The field `PReadyPollFacts.lag_corr`**. -/
theorem PReadyPollFacts_lag_corr :
    ∀ {g y : Nat} {d : Mma.D} {k : Fin 4}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .pWait k →
    leadCta (ctaOf L y) = ctaOf L g → 8 ≤ warpOf L y → warpOf L y < 12 →
    arrivals (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr y) ≤
      okPolls (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr g) →
      Lags L X y g (.inr (.mma d)) := by
  intro g y d k hg hy hσ hs hlead hw1 hw2 hle hub
  obtain ⟨ht1, hiT, hp, hW⟩ :=
    ready_waiter hpre hX ht hub (b := .pReady (Mma.stOf k)) hg hσ (.inl ⟨hs, rfl⟩)
  change okPolls (pReadyBar L (ctaOf L g) (k.val % 2)) (X.tr g) = _ at hp
  have hT : Work.T L y = Work.T L g :=
    T_eq_of_pair hpre (by simp only [leadCta] at hlead; omega)
  have hn1 := n_pos hpre
  have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
    rw [hW]; exact le_slotTime_of (by simp only [Time.bandM, Time.base]; omega)
  have hk2 : k.val % 2 < 2 := Nat.mod_lt _ (by decide)
  refine lags_corr hpre hX ht hub hy ⟨hw1, hw2⟩
    (arrivesOn (pReadyBar L (ctaOf L g) (k.val % 2))) (Work.n L * d.i + d.t + 1)
    (stateTime L g (.inr (.mma d)) - 2) (by omega) (fun c es _ hJc hinvc hcnt => ?_)
    (by change arrivals _ _ < _; omega) (by omega)
  have h := hJc.free (k.val % 2) hk2
  have hl : Correction.leadLoc L y (144 + 8 * (k.val % 2)) =
      pReadyBar L (ctaOf L g) (k.val % 2) := by
    simp only [Correction.leadLoc, pReadyBar, Correction.sb]
    simp only [leadCta] at hlead
    congr 1
    omega
  rw [hl] at h
  change es.countP _ = _ at h
  have hn : Correction.trips L = Work.n L := rfl
  rw [hn] at h
  have hlt := mul_add_lt (m := Work.n L) (a := c.i) (b := d.i)
    (x := Correction.freePos L (k.val % 2) c) (y := d.t + 1) ht1 (by omega)
  obtain ⟨h1, h2⟩ := corr_free_lt hinvc hn1 (o := Time.bandM + Time.mmaOff d.site) hk2 ht1
    (by rw [Correction.items_eq, hT]; exact hiT) (by omega)
  rw [hW]
  exact ⟨by omega, h2⟩

open Lag in
/-- **The field `P2PollFacts.lag_soft`**. -/
theorem P2PollFacts_lag_soft :
    ∀ {g y : Nat} {d : Mma.D} {k : Fin 4} {lead : Bool}, g < L.threads →
    y < L.threads → St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    d.site = .p2Wait k lead → leadCta (ctaOf L y) = ctaOf L g → warpOf L y < 8 →
    warpOf L y / 4 = k.val % 2 → SelfElected L X y →
    arrivals (pReady2Bar L (ctaOf L g) (k.val % 2)) (X.tr y) ≤
      okPolls (pReady2Bar L (ctaOf L g) (k.val % 2)) (X.tr g) →
      Lags L X y g (.inr (.mma d)) := by
  intro g y d k lead hg hy hσ hs hlead hw hst hse hle hub
  obtain ⟨ht1, hiT, hp, hW⟩ :=
    ready_waiter hpre hX ht hub (b := .pReady2 (Mma.stOf k)) hg hσ (.inr ⟨lead, hs, rfl⟩)
  change okPolls (pReady2Bar L (ctaOf L g) (k.val % 2)) (X.tr g) = _ at hp
  have hT : Work.T L y = Work.T L g :=
    T_eq_of_pair hpre (by simp only [leadCta] at hlead; omega)
  have hn1 := n_pos hpre
  have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
    rw [hW]; exact le_slotTime_of (by simp only [Time.bandM, Time.base]; omega)
  refine lags_soft hpre hX ht hub hy hw (arrivesOn (pReady2Bar L (ctaOf L g) (k.val % 2)))
    (Work.n L * d.i + d.t + 1) (stateTime L g (.inr (.mma d)) - 2) (by omega)
    (fun c es hk0 hJc hinvc hcnt => ?_) (by change arrivals _ _ < _; omega) (by omega)
  obtain ⟨j, rfl⟩ := hk0
  have h := hJc.pReady2 (electLead_of_self hse j)
  have hl : Softmax.leadLoc L y (160 + 8 * Softmax.stOf L y) =
      pReady2Bar L (ctaOf L g) (k.val % 2) := by
    simp only [Softmax.leadLoc, pReady2Bar, Softmax.sb, Softmax.stOf, hst]
    simp only [leadCta] at hlead
    congr 1
    omega
  rw [hl] at h
  change List.countP _ _ = _ at h
  have hn : Softmax.trips L = Work.n L := rfl
  rw [hn] at h
  have hlt := mul_add_lt (m := Work.n L) (a := c.i) (b := d.i) (x := Softmax.p2Pos c)
    (y := d.t + 1) ht1 (by omega)
  obtain ⟨h1, h2⟩ := soft_ready_lt hinvc hn1 (st := Softmax.stOf L y)
    (o := Time.bandM + Time.mmaOff d.site) (by simp only [Softmax.stOf]; omega) ht1
    (by simp only [Softmax.items]; rw [hT]; exact hiT) (by omega)
  rw [hW]
  exact ⟨by omega, h2⟩
end
end PTX.Kernels.FlashAttn4Fwd.Proof
