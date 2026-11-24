-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarCorr

@[expose] public section

/-! # The per-warp schedules of every named barrier (`Cross.BarSched`)

The schedule of barrier `id` for warp `w` of CTA `c` (`barS`) is its role's: barrier 2 at `b2S`
for the softmax and correction warps and at `b2M` for the MMA warp; the softmax warp's statistics
barrier `w + 3` at `statS` with offset `bandS (w / 4) + 22`; the correction warp's barriers
`w - 5` and `w - 1` (its stages 0 and 1) at `statS` with offset `bandC st`, `+2` in an item's last
slot. Each warp's events are at their times (`barCollSched`, from `barCnt`, `fired_barId` and the
roles' site tables). A thread waits only at a `bar.sync`: on barrier 2 the participants' start
barrier (ordinal 0, all at `bar0T`) and the MMA warp's second one (ordinal 1, after the arrivals
of the end barrier); on a statistics barrier the correction warp's syncs, after the softmax
warp's arrivals of the same ordinal (band `S st` before band `C st`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The MMA warp's barrier 2 -/

/-- The MMA warp's barrier sites. -/
def Mma.isB2 : Mma.Site → Bool
  | .bar0 | .bar1 => true
  | _ => false

theorem Mma.item_b2 {s : Mma.Site} (hs : Mma.ItemSite s) : Mma.bar2A s = 1 ∧ Mma.isB2 s = false :=
  by cases s <;> simp_all [Mma.ItemSite, Mma.bar2A, Mma.isB2]

/-- **The MMA warp's sites against barrier 2's schedule.** -/
theorem Mma.b2_time (hpre : Pre P L mem0) {g : Nat} {d : Mma.D} (hi : Mma.Inv L g d) :
    (Mma.isB2 d.site = true →
      mma (Work.n L) (Work.T L g) d = b2M (Work.n L) (Work.T L g) (Mma.bar2A d.site)) ∧
    (Mma.isB2 d.site = false →
      mma (Work.n L) (Work.T L g) d < b2M (Work.n L) (Work.T L g) (Mma.bar2A d.site)) := by
  by_cases hI : Mma.ItemSite d.site
  · obtain ⟨h1, h2⟩ := Mma.item_b2 hI
    rw [h1, h2]
    exact ⟨fun h => absurd h (by simp),
      fun _ => (Mma.time_item hpre hi hI).2.trans (Progress.Time.tail_lt (by decide))⟩
  · obtain ⟨s, i, t, b, pro⟩ := d
    cases s <;> simp only [Mma.ItemSite, not_true_eq_false] at hI
    all_goals simp only [mma, Mma.bar2A, Mma.isB2, b2M, reduceCtorEq, IsEmpty.forall_iff,
      true_and, and_true, Bool.false_eq_true, forall_const]
    all_goals first
      | decide
      | exact Progress.Time.fixed_lt (by decide)
      | exact Progress.Time.tail_lt (by decide)


/-! ### The schedule -/

/-- The schedule of named barrier `id` for warp `cw.2` of CTA `cw.1`. -/
def barS (L : Launch) (id : Nat) (cw : Nat × Nat) (k : Nat) : Nat :=
  if cw.2 < 8 then
    (if id = 2 then b2S (Work.n L) (Tc L cw.1) k
      else statS (Work.n L) (Tc L cw.1) (bandS (cw.2 / 4) + 22) 0 k)
  else if cw.2 < 12 then
    (if id = 2 then b2S (Work.n L) (Tc L cw.1) k
      else if id = cw.2 - 5 then statS (Work.n L) (Tc L cw.1) (bandC 0) 2 k
      else statS (Work.n L) (Tc L cw.1) (bandC 1) 2 k)
  else b2M (Work.n L) (Tc L cw.1) k

theorem barS_mono (L : Launch) (id : Nat) (cw : Nat × Nat) (k : Nat) :
    barS L id cw k < barS L id cw (k + 1) := by
  unfold barS
  split_ifs with h1 h2 h3 h4 h5
  · exact b2S_mono _ _ k
  · exact statS_mono (by simp only [bandS, span]; omega) k
  · exact b2S_mono _ _ k
  · exact statS_mono (by decide) k
  · exact statS_mono (by decide) k
  · exact b2M_mono _ _ k

theorem barGroup_lt {id w : Nat} (h : BarGroup id w) : w < 13 := by
  rcases h with ⟨-, h⟩ | ⟨st, k, hst, hk, -, h | h⟩ <;> omega

theorem barGroup_soft {id w : Nat} (h : BarGroup id w) (hw : w < 8) : id = 2 ∨ id = w + 3 := by
  rcases h with ⟨h, -⟩ | ⟨st, k, hst, hk, rfl, h | h⟩
  · exact .inl h
  · right; simp only [statsId]; omega
  · omega

theorem barGroup_corr {id w : Nat} (h : BarGroup id w) (hw : 8 ≤ w) (hw' : w < 12) :
    id = 2 ∨ id = w - 5 ∨ id = w - 1 := by
  rcases h with ⟨h, -⟩ | ⟨st, k, hst, hk, rfl, h | h⟩
  · exact .inl h
  · omega
  · right; simp only [statsId]; omega

theorem barGroup_mma {id : Nat} (h : BarGroup id 12) : id = 2 := by
  rcases h with ⟨h, -⟩ | ⟨st, k, hst, hk, rfl, h | h⟩ <;> omega

theorem barS_ge (L : Launch) (id : Nat) (cw : Nat × Nat) (k : Nat) : bar0T ≤ barS L id cw k := by
  have h1 : ∀ n T k, bar0T ≤ b2S n T k := fun n T k => by
    match k with
    | 0 => exact le_rfl
    | 1 => exact (Progress.Time.fixed_lt (by decide)).le
    | k + 2 => exact (Progress.Time.fixed_lt (by decide)).le
  have h2 : ∀ n T k, bar0T ≤ b2M n T k := fun n T k => by
    match k with
    | 0 => exact le_rfl
    | 1 => exact (Progress.Time.fixed_lt (by decide)).le
    | k + 2 => exact (Progress.Time.fixed_lt (by decide)).le
  unfold barS
  split_ifs
  all_goals first | exact h1 _ _ _ | exact h2 _ _ _ | exact (fixed_lt_statS (by decide)).le

theorem barS_zero (L : Launch) (cw : Nat × Nat) : barS L 2 cw 0 = bar0T := by
  unfold barS; split_ifs <;> first | rfl | (exfalso; omega)

theorem barS_one (L : Launch) (cw : Nat × Nat) :
    barS L 2 cw 1 ≤ b2M (Work.n L) (Tc L cw.1) 1 := by
  unfold barS
  split_ifs
  all_goals first | exact le_rfl | exact b2S_le_b2M _ _ le_rfl | (exfalso; omega)

theorem statS_le {n T a b a' b' c : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    statS n T a b c ≤ statS n T a' b' c := by
  unfold statS; split_ifs <;> omega

/-! ### The sites against the schedules -/

theorem soft_isB2 (L : Launch) (g : Nat) (s : Softmax.D) :
    (barIdOf L g (.inr (.softmax s)) == some 2) = Soft.isB2 s.site := by
  cases h : s.site <;> simp [barIdOf, Soft.isB2, h]

theorem soft_isGen (L : Launch) (g : Nat) (s : Softmax.D) :
    (barIdOf L g (.inr (.softmax s)) == some (warpOf L g + 3)) = Soft.isGen s.site := by
  cases h : s.site <;> simp [barIdOf, Soft.isGen, h]

theorem corr_isB2 (L : Launch) (g : Nat) (c : Correction.D) (hw : 8 ≤ warpOf L g) :
    (barIdOf L g (.inr (.corr c)) == some 2) = Corr.isB2 c.site := by
  cases h : c.site <;> simp [barIdOf, Corr.isB2, h]
  omega

theorem corr_isSync (L : Launch) (g : Nat) (c : Correction.D) (hw : 8 ≤ warpOf L g) (st : Nat)
    (hst : st < 2) :
    (barIdOf L g (.inr (.corr c)) == some (warpOf L g - 5 + 4 * st)) = Corr.isSync st c.site := by
  cases h : c.site <;> simp [barIdOf, Corr.isSync, h] <;> omega

theorem mma_isB2 (L : Launch) (g : Nat) (m : Mma.D) :
    (barIdOf L g (.inr (.mma m)) == some 2) = Mma.isB2 m.site := by
  cases h : m.site <;> simp [barIdOf, Mma.isB2, h]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
