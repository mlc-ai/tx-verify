-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedSoftWarpCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpQuiet

@[expose] public section

/-! # The softmax tiles' warp collectives against the schedule

A softmax tile makes two warp collectives, its warp barrier (`+38` of its slot in the band of
the warp's stage, `Time.softmax`) and its election (`+40`). An item has `n` tiles, tile `τ` in
slot `τ`; before a softmax state the role has made `2 n i + wbPos d + elPos d` of them
(`Softmax.Counts.warpBar`, `Softmax.Counts.elects`). The role's `r`-th collective is collective
`r % 2` of tile `m = r / 2` of the cluster's run, in global slot `m + m / n` (`wS`); past the
cluster's items the schedule is in the tail, after every softmax state, two apart. A state at a
warp barrier or an election is at its collective's time; every other state is before the next
collective: earlier in its slot, or the next tile is in a later slot (`role_time`). All these
times are even (`wS_even`, `soft_even`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section

namespace SoftW

/-- The time of the role's `r`-th warp collective of a softmax warp of stage `st` in a cluster
of `T` items of `n` tiles. -/
def wS (n T st r : Nat) : Nat :=
  if r < 2 * (n * T) then base + span * (r / 2 + r / 2 / n) + (bandS st + 38 + 2 * (r % 2))
  else tailTime n T (4000 + 600 * st + 2 * (r - 2 * (n * T)))

/-- Collective `p` of tile `τ < n` of item `i < T`. -/
theorem wS_at {n T st i τ p : Nat} (hi : i < T) (hτ : τ < n) (hp : p < 2) :
    wS n T st (2 * n * i + (2 * τ + p)) = slotTime n i τ (bandS st + 38 + 2 * p) := by
  have hn : 0 < n := by omega
  have h2 : 2 * n * i = 2 * (n * i) := by ring
  have hlt : 2 * n * i + (2 * τ + p) < 2 * (n * T) := by
    have : n * (i + 1) ≤ n * T := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at this
    omega
  have h1 : (2 * n * i + (2 * τ + p)) / 2 = n * i + τ := by rw [h2]; omega
  have h3 : (2 * n * i + (2 * τ + p)) % 2 = p := by rw [h2]; omega
  have h4 : (n * i + τ) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hτ, Nat.zero_add]
  simp only [wS, hlt, ↓reduceIte, h1, h3, h4, slotTime, gslot]
  ring

/-- Past the cluster's items the schedule is in the tail. -/
theorem wS_tail {n T st : Nat} : wS n T st (2 * n * T) = tailTime n T (4000 + 600 * st) := by
  have : 2 * n * T = 2 * (n * T) := by ring
  simp [wS, this]

/-- Consecutive collectives are more than one apart. -/
theorem wS_gap (n T st r : Nat) : wS n T st r + 1 < wS n T st (r + 1) := by
  unfold wS
  by_cases h1 : r + 1 < 2 * (n * T)
  · have h0 : r < 2 * (n * T) := by omega
    simp only [h0, h1, ↓reduceIte]
    by_cases hp : r % 2 = 0
    · have hq : (r + 1) / 2 = r / 2 := by omega
      have hr : (r + 1) % 2 = 1 := by omega
      rw [hq, hr, hp]
      omega
    · have hq : (r + 1) / 2 = r / 2 + 1 := by omega
      rw [hq]
      have : r / 2 / n ≤ (r / 2 + 1) / n := Nat.div_le_div_right (by omega)
      have : span * (r / 2 + r / 2 / n) + span ≤ span * (r / 2 + 1 + (r / 2 + 1) / n) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      simp only [bandS, span] at *
      omega
  · simp only [h1, ↓reduceIte]
    by_cases h0 : r < 2 * (n * T)
    · simp only [h0, ↓reduceIte]
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at h0
        · exact h
      have hm : r / 2 < n * T := by omega
      have hmn : r / 2 / n < T := (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm]; exact hm)
      unfold tailTime slotTime gslot
      have : span * (r / 2 + r / 2 / n) + span * 2 ≤ span * (T * (n + 1) + 0) := by
        rw [← Nat.mul_add]
        refine Nat.mul_le_mul_left _ ?_
        have : n * T = T * n := Nat.mul_comm _ _
        rw [Nat.mul_succ]
        omega
      simp only [bandS, span] at *
      omega
    · simp only [h0, ↓reduceIte]
      unfold tailTime slotTime
      omega

theorem wS_even (n T st r : Nat) : wS n T st r % 2 = 0 := by
  unfold wS
  split_ifs
  · simp only [base, span, bandS]; omega
  · exact slot_even (by omega)

theorem wS_ge (n T st r : Nat) : base ≤ wS n T st r := by
  unfold wS
  split_ifs
  · omega
  · exact Progress.Time.base_le

/-- Before the next tile: a time in slot `τ < n` of item `i < T` is before the next tile's warp
barrier. -/
theorem next_tile {n T st i τ o : Nat} (hi : i < T) (hτ : τ < n) (ho : o < span) :
    slotTime n i τ o < wS n T st (2 * n * i + 2 * (τ + 1)) := by
  by_cases h : τ + 1 < n
  · rw [show 2 * (τ + 1) = 2 * (τ + 1) + 0 by rfl, wS_at hi h (by decide)]
    exact Progress.Time.lt_of_slot (by omega) ho
  · have hτ' : τ + 1 = n := by omega
    rw [hτ', show 2 * n * i + 2 * n = 2 * n * (i + 1) by ring]
    by_cases hT : i + 1 < T
    · rw [show 2 * n * (i + 1) = 2 * n * (i + 1) + (2 * 0 + 0) by ring,
        wS_at hT (by omega) (by decide)]
      exact Progress.Time.lt_of_item (by omega) (by omega) ho
    · rw [show i + 1 = T by omega, wS_tail]
      exact Progress.Time.lt_tail (by omega) hi ho

/-- The end of an item: a time in slot `s ≤ n` of item `i < T` is before the next item's first
collective. -/
theorem next_item {n T st i s o : Nat} (hn : 0 < n) (hi : i < T) (hs : s ≤ n) (ho : o < span) :
    slotTime n i s o < wS n T st (2 * n * i + 2 * n) := by
  rw [show 2 * n * i + 2 * n = 2 * n * (i + 1) by ring]
  by_cases hT : i + 1 < T
  · rw [show 2 * n * (i + 1) = 2 * n * (i + 1) + (2 * 0 + 0) by ring,
      wS_at hT hn (by decide)]
    exact Progress.Time.lt_of_item hs (by omega) ho
  · rw [show i + 1 = T by omega, wS_tail]
    exact Progress.Time.lt_tail hs hi ho

/-- Before the tile's warp barrier. -/
theorem at_lt {n T st i τ o : Nat} (hi : i < T) (hτ : τ < n) (ho : o < 38) :
    slotTime n i τ (bandS st + o) < wS n T st (2 * n * i + 2 * τ) := by
  rw [show 2 * τ = 2 * τ + 0 by rfl, wS_at hi hτ (by decide)]
  exact Progress.Time.lt_of_off (by omega)

/-- Before the item's first warp barrier. -/
theorem at_lt0 {n T st i o : Nat} (hi : i < T) (hn : 0 < n) (ho : o < 38) :
    slotTime n i 0 (bandS st + o) < wS n T st (2 * n * i) := by
  have := at_lt (st := st) (τ := 0) hi hn ho
  simpa using this

/-- **The softmax sites against the schedule**: the role's collectives before a state are
`2 n i + wbPos d + elPos d`. -/
theorem role_time {L : Launch} {g : Nat} {d : Softmax.D} (hn : 0 < Work.n L)
    (hi : Softmax.Inv L g d) {st : Nat} (hst : st < 2) :
    (softmaxKind d.site = .warp → softmax (Work.n L) (Work.T L g) st d =
      wS (Work.n L) (Work.T L g) st (2 * Work.n L * d.i + Softmax.wbPos d + Softmax.elPos d)) ∧
    (softmaxKind d.site ≠ .warp → softmax (Work.n L) (Work.T L g) st d <
      wS (Work.n L) (Work.T L g) st (2 * Work.n L * d.i + Softmax.wbPos d + Softmax.elPos d)) := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  have hitem := hi.item
  have htail := hi.tail
  have hstart := hi.start
  have htrip := hi.trip
  have hlast := hi.last
  simp only at hitem htail hstart htrip hlast
  have hN : Softmax.trips L = Work.n L := rfl
  have hI : Softmax.items L g = Work.T L g := rfl
  rw [hN] at htrip hlast
  rw [hI] at hitem htail
  have hb : ∀ o, o < 600 → bandS st + o < span := fun o ho => by simp only [bandS, span]; omega
  have hsl : ∀ lp : Bool, (lp = true → t + 1 < Work.n L) → (if lp then t + 1 else 0) < Work.n L :=
    fun lp h => by cases lp <;> simp_all
  cases site with
  | setMaxReg | bar0 =>
    obtain ⟨rfl, rfl⟩ := hstart (by simp)
    simp only [softmax, softmaxKind, Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0,
      Softmax.Site.inTrip, Nat.mul_zero]
    refine ⟨by simp, fun _ => ?_⟩
    refine lt_of_lt_of_le ?_ (wS_ge _ _ _ _)
    simp only [regT, bar0T, base]
    omega
  | statsW w =>
    rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
    · have hiT := hitem rfl
      simp only [softmax, softmaxKind]
      refine ⟨by simp, fun _ => ?_⟩
      simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.tileNo,
        Softmax.Site.afterWB, Softmax.Site.afterEl]
      simpa using at_lt0 (st := st) (o := 0) hiT hn (by decide)
    · have hiT := hitem rfl
      simp only [softmax, softmaxKind]
      refine ⟨by simp, fun _ => ?_⟩
      simp only [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.tileNo,
        Softmax.Site.afterWB, Softmax.Site.afterEl, Bool.true_or, ↓reduceIte]
      rw [show 2 * Work.n L * i + (0 + 1) + (0 + 1) = 2 * Work.n L * i + 2 * (0 + 1) by ring]
      by_cases h1 : 1 < Work.n L
      · rw [show 2 * (0 + 1) = 2 * 1 by rfl]
        exact at_lt (τ := 1) hiT h1 (by decide)
      · have h1' : Work.n L = 1 := by omega
        rw [h1']
        exact next_item (by decide) hiT le_rfl (hb _ (by decide))
    · have hiT := hitem rfl
      have ht := htrip rfl
      simp only [softmax, softmaxKind]
      refine ⟨by simp, fun _ => ?_⟩
      simp only [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
        Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl, Bool.false_or,
        Bool.true_or, ↓reduceIte, Bool.false_eq_true]
      rw [show 2 * Work.n L * i + (t + 1 + 1) + (t + 1 + 1) = 2 * Work.n L * i + 2 * (t + 2) by
        ring]
      by_cases h1 : t + 2 < Work.n L
      · exact at_lt hiT h1 (by decide)
      · rw [show 2 * (t + 2) = 2 * Work.n L by omega]
        exact next_item hn hiT (by omega) (hb _ (by decide))
    · obtain ⟨rfl, rfl⟩ := htail (by simp)
      simp only [softmax, softmaxKind]
      refine ⟨by simp, fun _ => ?_⟩
      simp only [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip]
      simp only [Bool.false_eq_true, Bool.or_false, reduceCtorEq, decide_false, ↓reduceIte,
        Nat.add_zero, wS_tail]
      exact Progress.Time.tail_lt (by simp only [bandS]; omega)
  | sW lp =>
    simp only [softmax, softmaxKind, softSlot]
    refine ⟨by simp, fun _ => ?_⟩
    have hτ := hsl lp fun h => htrip (by subst h; rfl)
    have hiT := hitem rfl
    cases lp <;> simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl] at hτ ⊢
    · exact at_lt0 hiT hτ (by decide)
    · rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * (t + 1) by ring]
      exact at_lt hiT hτ (by decide)
  | ld lp c | ldW lp c | pst lp c =>
    simp only [softmax, softmaxKind, softSlot]
    refine ⟨by simp, fun _ => ?_⟩
    have hτ := hsl lp fun h => htrip (by subst h; rfl)
    have hiT := hitem rfl
    have hc := c.isLt
    cases lp <;> simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl] at hτ ⊢
    all_goals first
      | exact at_lt0 hiT hτ (by first | omega | (split_ifs <;> omega))
      | (rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * (t + 1) by ring]
         exact at_lt hiT hτ (by first | omega | (split_ifs <;> omega)))
  | pwait lp h =>
    simp only [softmax, softmaxKind, softSlot]
    refine ⟨by simp, fun _ => ?_⟩
    have hτ := hsl lp fun h => htrip (by subst h; rfl)
    have hiT := hitem rfl
    have hh := h.isLt
    cases lp <;> simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl] at hτ ⊢
    · exact at_lt0 hiT hτ (by omega)
    · rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * (t + 1) by ring]
      exact at_lt hiT hτ (by omega)
  | pArr lp =>
    simp only [softmax, softmaxKind, softSlot]
    refine ⟨by simp, fun _ => ?_⟩
    have hτ := hsl lp fun h => htrip (by subst h; rfl)
    have hiT := hitem rfl
    cases lp <;> simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl] at hτ ⊢
    · exact at_lt0 hiT hτ (by decide)
    · rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * (t + 1) by ring]
      exact at_lt hiT hτ (by decide)
  | alphaSt =>
    simp only [softmax, softmaxKind]
    refine ⟨by simp, fun _ => ?_⟩
    simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl]
    rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * (t + 1) by ring]
    exact at_lt (hitem rfl) (htrip rfl) (by decide)
  | gen j =>
    rcases Softmax.fin3_cases j with rfl | rfl | rfl
    · simp only [softmax, softmaxKind]
      refine ⟨by simp, fun _ => ?_⟩
      simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.tileNo,
        Softmax.Site.afterWB, Softmax.Site.afterEl]
      exact at_lt0 (hitem rfl) hn (by decide)
    · simp only [softmax, softmaxKind]
      refine ⟨by simp, fun _ => ?_⟩
      simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
        Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl]
      rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * (t + 1) by ring]
      exact at_lt (hitem rfl) (htrip rfl) (by decide)
    · have hl := hlast (.inr rfl)
      simp only [softmax, softmaxKind]
      refine ⟨by simp, fun _ => ?_⟩
      simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
        Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl]
      rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * Work.n L by omega]
      exact next_item hn (hitem rfl) le_rfl (hb _ (by decide))
  | lSt =>
    have hl := hlast (.inl rfl)
    simp only [softmax, softmaxKind]
    refine ⟨by simp, fun _ => ?_⟩
    simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl]
    rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + 2 * Work.n L by omega]
    exact next_item hn (hitem rfl) le_rfl (hb _ (by decide))
  | warpBar lp =>
    simp only [softmax, softmaxKind, softSlot]
    refine ⟨fun _ => ?_, by simp⟩
    have hτ := hsl lp fun h => htrip (by subst h; rfl)
    have hiT := hitem rfl
    cases lp <;> simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl] at hτ ⊢
    · rw [show 2 * Work.n L * i = 2 * Work.n L * i + (2 * 0 + 0) by ring, wS_at hiT hτ
        (by decide)]
    · rw [show 2 * Work.n L * i + (t + 1) + (t + 1) = 2 * Work.n L * i + (2 * (t + 1) + 0) by
        ring, wS_at hiT hτ (by decide)]
  | el lp =>
    simp only [softmax, softmaxKind, softSlot]
    refine ⟨fun _ => ?_, by simp⟩
    have hτ := hsl lp fun h => htrip (by subst h; rfl)
    have hiT := hitem rfl
    cases lp <;> simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl] at hτ ⊢
    · rw [show 2 * Work.n L * i + 1 = 2 * Work.n L * i + (2 * 0 + 1) by ring, wS_at hiT hτ
        (by decide)]
    · rw [show 2 * Work.n L * i + (t + 1 + 1) + (t + 1) = 2 * Work.n L * i + (2 * (t + 1) + 1)
        by ring, wS_at hiT hτ (by decide)]
  | p2Arr lp =>
    simp only [softmax, softmaxKind, softSlot]
    refine ⟨by simp, fun _ => ?_⟩
    have hτ := hsl lp fun h => htrip (by subst h; rfl)
    have hiT := hitem rfl
    cases lp <;> simp [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.tileNo, Softmax.Site.afterWB, Softmax.Site.afterEl] at hτ ⊢
    · rw [show 2 * Work.n L * i + 1 + 1 = 2 * Work.n L * i + 2 * (0 + 1) by ring]
      exact next_tile hiT hτ (hb _ (by decide))
    · rw [show 2 * Work.n L * i + (t + 1 + 1) + (t + 1 + 1) = 2 * Work.n L * i + 2 * (t + 1 + 1)
        by ring]
      exact next_tile hiT hτ (hb _ (by decide))
  | barEnd | exit =>
    obtain ⟨rfl, rfl⟩ := htail (by simp)
    simp only [softmax, softmaxKind]
    refine ⟨by simp, fun _ => ?_⟩
    simp only [Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip]
    simp only [Bool.false_eq_true, Bool.or_false, reduceCtorEq, decide_false, ↓reduceIte,
      Nat.add_zero, wS_tail]
    exact Progress.Time.tail_lt (by omega)

/-- The softmax times are even. -/
theorem soft_even (n T st : Nat) (d : Softmax.D) : softmax n T st d % 2 = 0 := by
  obtain ⟨s, i, t, w, m, l⟩ := d
  cases s <;> simp only [softmax, tailTime, regT, bar0T]
  all_goals (try split)
  all_goals (try decide)
  all_goals refine slot_even ?_
  all_goals (try simp only [bandS])
  all_goals (try split_ifs)
  all_goals omega

end SoftW

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
