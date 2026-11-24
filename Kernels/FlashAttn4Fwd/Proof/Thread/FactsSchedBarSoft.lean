-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarTime

@[expose] public section

/-! # The softmax warps' named-barrier schedules against their site table

Barrier 2: the start barrier at `bar0T`, every item site and the tail's credit poll before the
end arrival at `tailTime … 2000` (`time_item`), the exit after it (`b2_time`). The statistics
barrier: the `gen` of a tile is at offset `+22` of the tile's slot; before it in the slot the
polls and the loads, after it (in a later slot of the schedule) the stores, the arrivals and the
election (`gen_time`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Soft

/-- **Every item site of a softmax warp is before the tail.** -/
theorem time_item {g st : Nat} {d : Softmax.D} (hn : 0 < Work.n L) (hi : Softmax.Inv L g d)
    (hst : st < 2) (hin : d.site.inItem = true) :
    softmax (Work.n L) (Work.T L g) st d < tailTime (Work.n L) (Work.T L g) 0 := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  have hiT : i < Work.T L g := hi.item hin
  have htrip := hi.trip
  have hlast := hi.last
  simp only at htrip hlast hin
  have hN : Softmax.trips L = Work.n L := rfl
  rw [hN] at htrip hlast
  have hb : ∀ o, o < 600 → bandS st + o < span := fun o ho => by simp only [bandS, span]; omega
  have hsl : ∀ lp : Bool, (lp = true → t + 1 < Work.n L) →
      softSlot ⟨site, i, t, w, m, l⟩ lp ≤ Work.n L := fun lp h => by
    unfold softSlot; cases lp
    · simp
    · simpa using (h rfl).le
  cases site with
  | setMaxReg | bar0 | barEnd | exit => simp [Softmax.Site.inItem] at hin
  | statsW w =>
    rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
    · exact Progress.Time.lt_tail (by omega) hiT (hb _ (by decide))
    · exact Progress.Time.lt_tail (by omega) hiT (hb _ (by decide))
    · exact Progress.Time.lt_tail
        (by have h1 := htrip rfl; dsimp only; change t + 1 < Work.n L at h1; omega) hiT
        (hb _ (by decide))
    · simp [Softmax.Site.inItem] at hin
  | sW lp | pArr lp | warpBar lp | el lp | p2Arr lp =>
    exact Progress.Time.lt_tail (hsl lp fun h => htrip (by subst h; rfl)) hiT (hb _ (by decide))
  | ld lp c | ldW lp c =>
    exact Progress.Time.lt_tail (hsl lp fun h => htrip (by subst h; rfl)) hiT (hb _ (by omega))
  | pst lp c =>
    exact Progress.Time.lt_tail (hsl lp fun h => htrip (by subst h; rfl)) hiT
      (hb _ (by split_ifs <;> omega))
  | pwait lp h =>
    exact Progress.Time.lt_tail (hsl lp fun h => htrip (by subst h; rfl)) hiT (hb _ (by omega))
  | alphaSt =>
    exact Progress.Time.lt_tail
      (by have h1 := htrip rfl; dsimp only; change t + 1 < Work.n L at h1; omega) hiT
      (hb _ (by decide))
  | lSt => exact Progress.Time.lt_tail le_rfl hiT (hb _ (by decide))
  | gen j =>
    rcases Softmax.fin3_cases j with rfl | rfl | rfl
    · exact Progress.Time.lt_tail (by omega) hiT (hb _ (by decide))
    · exact Progress.Time.lt_tail
        (by have h1 := htrip rfl; dsimp only; change t + 1 < Work.n L at h1; omega) hiT
        (hb _ (by decide))
    · exact Progress.Time.lt_tail le_rfl hiT (hb _ (by decide))

/-- The start and end barriers. -/
def isB2 : Softmax.Site → Bool
  | .bar0 | .barEnd => true
  | _ => false

/-- **The softmax sites against barrier 2's schedule.** -/
theorem b2_time {g st : Nat} {d : Softmax.D} (hn : 0 < Work.n L) (hi : Softmax.Inv L g d)
    (hst : st < 2) :
    (isB2 d.site = true → softmax (Work.n L) (Work.T L g) st d =
      b2S (Work.n L) (Work.T L g) (Softmax.bar2Sync d + Softmax.bar2Arrive d)) ∧
    (isB2 d.site = false → softmax (Work.n L) (Work.T L g) st d <
      b2S (Work.n L) (Work.T L g) (Softmax.bar2Sync d + Softmax.bar2Arrive d)) := by
  by_cases hin : d.site.inItem = true
  · have h1 : isB2 d.site = false := by
      cases hs : d.site <;> simp_all [isB2, Softmax.Site.inItem]
    have h2 : Softmax.bar2Sync d + Softmax.bar2Arrive d = 1 := by
      cases hs : d.site <;> simp_all [Softmax.bar2Sync, Softmax.bar2Arrive, Softmax.Site.inItem]
    rw [h1, h2]
    exact ⟨fun h => absurd h (by simp),
      fun _ => (time_item hn hi hst hin).trans (Progress.Time.tail_lt (by decide))⟩
  · obtain ⟨site, i, t, w, m, l⟩ := d
    have htail := hi.tail
    simp only at htail
    cases site with
    | setMaxReg => simp only [softmax, isB2, Softmax.bar2Sync, Softmax.bar2Arrive, b2S]; decide
    | bar0 => simp only [softmax, isB2, Softmax.bar2Sync, Softmax.bar2Arrive, b2S]; decide
    | barEnd =>
      simp only [softmax, isB2, Softmax.bar2Sync, Softmax.bar2Arrive, b2S]
      exact ⟨fun _ => trivial, fun h => absurd h (by simp)⟩
    | exit =>
      simp only [softmax, isB2, Softmax.bar2Sync, Softmax.bar2Arrive, b2S]
      exact ⟨fun h => absurd h (by simp), fun _ => Progress.Time.tail_lt (by decide)⟩
    | statsW w =>
      rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
      all_goals simp [Softmax.Site.inItem] at hin
      simp only [softmax, isB2, Softmax.bar2Sync, Softmax.bar2Arrive, b2S]
      exact ⟨fun h => absurd h (by simp),
        fun _ => Progress.Time.tail_lt (by simp only [bandS]; omega)⟩
    | _ => simp [Softmax.Site.inItem] at hin

/-- The statistics barrier's sites. -/
def isGen : Softmax.Site → Bool
  | .gen _ => true
  | _ => false

/-- **The softmax sites against the statistics barrier's schedule.** -/
theorem gen_time {g st : Nat} {d : Softmax.D} (hn : 0 < Work.n L) (hi : Softmax.Inv L g d)
    (hst : st < 2) :
    let a := bandS st + 22
    let c := (Work.n L + 1) * d.i + Softmax.genPos d
    (isGen d.site = true → softmax (Work.n L) (Work.T L g) st d =
      statS (Work.n L) (Work.T L g) a 0 c) ∧
    (isGen d.site = false → softmax (Work.n L) (Work.T L g) st d <
      statS (Work.n L) (Work.T L g) a 0 c) := by
  intro a c
  obtain ⟨site, i, t, w, m, l⟩ := d
  have hitem := hi.item
  have htail := hi.tail
  have hstart := hi.start
  have htrip := hi.trip
  have hlast := hi.last
  have htile0 := hi.tile0
  simp only at hitem htail hstart htrip hlast htile0
  have hN : Softmax.trips L = Work.n L := rfl
  have hI : Softmax.items L g = Work.T L g := rfl
  rw [hN] at htrip hlast
  rw [hI] at hitem htail
  have hb : ∀ o, o < 600 → bandS st + o < span := fun o ho => by simp only [bandS, span]; omega
  simp only [a, c]
  cases site with
  | setMaxReg | bar0 =>
    obtain ⟨rfl, rfl⟩ := hstart (by simp)
    refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
    exact fixed_lt_statS (by simp [softmax, regT, bar0T, base])
  | barEnd | exit =>
    obtain ⟨rfl, rfl⟩ := htail (by simp)
    refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
    simp only [softmax, Softmax.genPos, Softmax.Site.tile0, Softmax.Site.inTrip]
    simp only [Bool.false_or, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero]
    exact tail_lt_statS (by decide)
  | statsW w =>
    rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
    · refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
      simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen]
      exact lt_same (hitem rfl) (by omega) (by simp) (by simp only [bandS]; split_ifs <;> omega)
    · refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
      simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen]
      exact lt_same (hitem rfl) (by omega) (by simp) (by simp only [bandS]; split_ifs <;> omega)
    · have ht := htrip rfl
      refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
      simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen, Softmax.Site.inTrip]
      exact lt_same (hitem rfl) (by omega) (by simp)
        (by simp only [bandS]; split_ifs <;> omega)
    · obtain ⟨rfl, rfl⟩ := htail (by simp)
      refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
      simp only [softmax, Softmax.genPos, Softmax.Site.tile0, Softmax.Site.inTrip]
      simp only [Bool.false_or, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero]
      exact tail_lt_statS (by simp only [bandS]; omega)
  | sW lp | ld lp _ | ldW lp _ =>
    refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
    cases lp
    · have ht0 := htile0 rfl
      simp only [softmax, softSlot, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen, Bool.false_eq_true, ↓reduceIte]
      exact lt_same (hitem rfl) (by omega) (by simp) (by simp only [bandS]; split_ifs <;> omega)
    · have ht := htrip rfl
      simp only [softmax, softSlot, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen, Softmax.Site.inTrip, Bool.false_eq_true, ↓reduceIte]
      exact lt_same (hitem rfl) (by omega) (by simp) (by simp only [bandS]; split_ifs <;> omega)
  | alphaSt =>
    have ht := htrip rfl
    refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
    simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
      Softmax.Site.afterGen, Softmax.Site.inTrip]
    exact lt_same (hitem rfl) (by omega) (by simp) (by simp only [bandS]; split_ifs <;> omega)
  | lSt =>
    have ht := hlast (by simp)
    refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
    simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
      Softmax.Site.afterGen, Softmax.Site.inTrip]
    exact lt_same (hitem rfl) le_rfl (by simp; omega) (by simp only [bandS]; omega)
  | gen j =>
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [isGen])⟩
    rcases Softmax.fin3_cases j with rfl | rfl | rfl
    · have ht0 := htile0 rfl
      simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen]
      exact eq_same (hitem rfl) (by omega) (by simp) (by split_ifs <;> omega)
    · have ht := htrip rfl
      simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen, Softmax.Site.inTrip]
      exact eq_same (hitem rfl) (by omega) (by simp) (by split_ifs <;> omega)
    · have ht := hlast (by simp)
      simp only [softmax, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen, Softmax.Site.inTrip]
      exact eq_same (hitem rfl) le_rfl (by simp; omega) (by simp)
  | pst lp _ | pwait lp _ | pArr lp | warpBar lp | el lp | p2Arr lp =>
    refine ⟨fun h => absurd h (by simp [isGen]), fun _ => ?_⟩
    cases lp
    · simp only [softmax, softSlot, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen, Bool.false_eq_true, ↓reduceIte]
      exact lt_statS (by simp) (hb _ (by first | omega | (split_ifs <;> omega)))
    · simp only [softmax, softSlot, Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.afterGen, Softmax.Site.inTrip, Bool.false_eq_true, ↓reduceIte]
      exact lt_statS (by simp) (hb _ (by first | omega | (split_ifs <;> omega)))

end Soft
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
