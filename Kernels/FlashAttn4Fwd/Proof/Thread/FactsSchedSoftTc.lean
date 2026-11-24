-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedMma

@[expose] public section

/-! # The softmax warps' warp-collective `tcgen05` schedule

A softmax tile makes fourteen warp-collective `tcgen05` events, at fixed offsets of its slot in
the band of the warp's stage (`Time.softmax`): the four loads and their waits (`+4 … +18`), three
stores (`+24`, `+26`, `+28`), the first store wait (`+30`), the fourth store (`+34`) and the second
wait (`+36`). An item has `n` tiles, tile `τ` in slot `τ`; before a state there are
`14 n i + tcPos d` such events (`tcPos`: the tile's earlier events, fourteen per earlier tile).
The `c`-th event is event `c % 14` of the item's tile `m = c / 14` of the cluster's run, in global
slot `m + m / n` (`tcS`); past the cluster's items the schedule is in the tail, after every
softmax state. A state at a collective site is at its event's time; every other state is before
the next event: earlier in its slot, or the next tile is in a later slot (`next_tile`).

The count is the softmax package's (`SoftTcCount`, `Softmax.tcColl_sched`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Soft

/-- The warp-collective `tcgen05` events of the item before a softmax state. -/
def tcPos (L : Launch) (d : Softmax.D) : Nat :=
  match d.site with
  | .setMaxReg | .bar0 | .statsW 0 | .statsW 3 | .barEnd | .exit => 0
  | .statsW 1 => 14
  | .statsW 2 => 14 * (d.t + 2)
  | .sW lp => 14 * softSlot d lp
  | .ld lp c => 14 * softSlot d lp + 2 * c.val
  | .ldW lp c => 14 * softSlot d lp + 2 * c.val + 1
  | .alphaSt => 14 * (d.t + 1) + 8
  | .gen 0 => 8
  | .gen 1 => 14 * (d.t + 1) + 8
  | .gen 2 | .lSt => 14 * Softmax.trips L
  | .pst lp c => 14 * softSlot d lp + (if c.val < 3 then 8 + c.val else 12)
  | .pwait lp h => 14 * softSlot d lp + (if h.val = 0 then 11 else 13)
  | .pArr lp => 14 * softSlot d lp + 12
  | .warpBar lp | .el lp | .p2Arr lp => 14 * softSlot d lp + 14

/-- The softmax package's count of its warp-collective `tcgen05` events at a state of the role
(`Softmax.tcColl_sched`, from `Counts.tcColl` and the invariant). -/
def SoftTcCount (L : Launch) : Prop :=
  ∀ {g : Nat} {d : Softmax.D} {es : List Event}, Softmax.Counts L g d es → Softmax.Inv L g d →
    es.countP isTcColl = 14 * Softmax.trips L * d.i + tcPos L d

/-- The offset of a tile's `p`-th event in its band. -/
def tcOff (p : Nat) : Nat :=
  if p < 8 then 4 + 2 * p else if p < 11 then 24 + 2 * (p - 8) else if p = 11 then 30
  else if p = 12 then 34 else 36

theorem tcOff_lt (p : Nat) : tcOff p ≤ 36 := by unfold tcOff; split_ifs <;> omega

theorem tcOff_mono {p : Nat} (hp : p < 13) : tcOff p < tcOff (p + 1) := by
  unfold tcOff; split_ifs <;> omega

/-- The time of the `c`-th warp-collective `tcgen05` event of a softmax warp of stage `st` in a
cluster of `T` items of `n` tiles. -/
def tcS (n T st c : Nat) : Nat :=
  if c < 14 * (n * T) then base + span * (c / 14 + c / 14 / n) + (bandS st + tcOff (c % 14))
  else tailTime n T (4000 + 600 * st + (c - 14 * (n * T)))

/-- The event of tile `τ < n` of item `i < T`. -/
theorem tcS_at {n T st i τ p : Nat} (hi : i < T) (hτ : τ < n) (hp : p < 14) :
    tcS n T st (14 * n * i + (14 * τ + p)) = slotTime n i τ (bandS st + tcOff p) := by
  have hn : 0 < n := by omega
  have h14 : 14 * n * i = 14 * (n * i) := by ring
  have hlt : 14 * n * i + (14 * τ + p) < 14 * (n * T) := by
    have : n * (i + 1) ≤ n * T := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at this
    omega
  have h1 : (14 * n * i + (14 * τ + p)) / 14 = n * i + τ := by rw [h14]; omega
  have h2 : (14 * n * i + (14 * τ + p)) % 14 = p := by rw [h14]; omega
  have h3 : (n * i + τ) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hτ, Nat.zero_add]
  simp only [tcS, hlt, ↓reduceIte, h1, h2, h3, slotTime, gslot]
  ring

/-- Past the cluster's items the schedule is in the tail. -/
theorem tcS_tail {n T st : Nat} :
    tcS n T st (14 * n * T) = tailTime n T (4000 + 600 * st) := by
  have : 14 * n * T = 14 * (n * T) := by ring
  simp [tcS, this]

theorem tcS_mono (n T st c : Nat) : tcS n T st c < tcS n T st (c + 1) := by
  unfold tcS
  have ho := tcOff_lt (c % 14)
  have ho' := tcOff_lt ((c + 1) % 14)
  by_cases h1 : c + 1 < 14 * (n * T)
  · have h0 : c < 14 * (n * T) := by omega
    simp only [h0, h1, ↓reduceIte]
    by_cases hp : c % 14 < 13
    · have hq : (c + 1) / 14 = c / 14 := by omega
      have hr : (c + 1) % 14 = c % 14 + 1 := by omega
      rw [hq, hr]
      have := tcOff_mono hp
      omega
    · have hq : (c + 1) / 14 = c / 14 + 1 := by omega
      rw [hq]
      have : c / 14 / n ≤ (c / 14 + 1) / n := Nat.div_le_div_right (by omega)
      have : span * (c / 14 + c / 14 / n) + span ≤ span * (c / 14 + 1 + (c / 14 + 1) / n) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      simp only [bandS, span] at *
      omega
  · simp only [h1, ↓reduceIte]
    by_cases h0 : c < 14 * (n * T)
    · simp only [h0, ↓reduceIte]
      have hc : c = 14 * (n * T) - 1 := by omega
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at h0
        · exact h
      have hm : c / 14 < n * T := by omega
      have hmn : c / 14 / n < T := (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm]; exact hm)
      unfold tailTime slotTime gslot
      have : span * (c / 14 + c / 14 / n) + span * 2 ≤ span * (T * (n + 1) + 0) := by
        rw [← Nat.mul_add]
        refine Nat.mul_le_mul_left _ ?_
        have : n * T = T * n := Nat.mul_comm _ _
        rw [Nat.mul_succ]
        omega
      simp only [bandS, span] at *
      omega
    · simp only [h0, ↓reduceIte]
      exact Progress.Time.tail_lt (by omega)

/-- Before the next tile: a time in slot `τ < n` of item `i < T` is before the first event of the
next tile. -/
theorem next_tile {n T st i τ o : Nat} (hi : i < T) (hτ : τ < n) (ho : o < span) :
    slotTime n i τ o < tcS n T st (14 * n * i + 14 * (τ + 1)) := by
  by_cases h : τ + 1 < n
  · rw [show 14 * (τ + 1) = 14 * (τ + 1) + 0 by rfl, tcS_at hi h (by decide)]
    exact Progress.Time.lt_of_slot (by omega) ho
  · have hτ' : τ + 1 = n := by omega
    rw [hτ', show 14 * n * i + 14 * n = 14 * n * (i + 1) by ring]
    by_cases hT : i + 1 < T
    · rw [show 14 * n * (i + 1) = 14 * n * (i + 1) + (14 * 0 + 0) by ring,
        tcS_at hT (by omega) (by decide)]
      exact Progress.Time.lt_of_item (by omega) (by omega) ho
    · rw [show i + 1 = T by omega, tcS_tail]
      exact Progress.Time.lt_tail (by omega) hi ho

/-- The end of an item: a time in slot `s ≤ n` of item `i < T` is before the next item's first
event. -/
theorem next_item {n T st i s o : Nat} (hn : 0 < n) (hi : i < T) (hs : s ≤ n) (ho : o < span) :
    slotTime n i s o < tcS n T st (14 * n * i + 14 * n) := by
  rw [show 14 * n * i + 14 * n = 14 * n * (i + 1) by ring]
  by_cases hT : i + 1 < T
  · rw [show 14 * n * (i + 1) = 14 * n * (i + 1) + (14 * 0 + 0) by ring,
      tcS_at hT hn (by decide)]
    exact Progress.Time.lt_of_item hs (by omega) ho
  · rw [show i + 1 = T by omega, tcS_tail]
    exact Progress.Time.lt_tail hs hi ho

theorem at_eq {n T st i τ p o : Nat} (hi : i < T) (hτ : τ < n) (hp : p < 14)
    (ho : tcOff p = o) :
    slotTime n i τ (bandS st + o) = tcS n T st (14 * n * i + (14 * τ + p)) := by
  rw [tcS_at hi hτ hp, ho]

theorem at_lt {n T st i τ p o : Nat} (hi : i < T) (hτ : τ < n) (hp : p < 14)
    (ho : o < tcOff p) :
    slotTime n i τ (bandS st + o) < tcS n T st (14 * n * i + (14 * τ + p)) := by
  rw [tcS_at hi hτ hp]
  exact Progress.Time.lt_of_off (by omega)

theorem softSlot_lt {d : Softmax.D} {n : Nat} (hn : 0 < n) (lp : Bool)
    (ht : lp = true → d.t + 1 < n) : softSlot d lp < n := by
  unfold softSlot; cases lp
  · simpa using hn
  · simpa using ht rfl

/-- **The softmax sites against the schedule.** -/
theorem tc_time {g : Nat} {d : Softmax.D} (hn : 0 < Work.n L) (hi : Softmax.Inv L g d)
    {st : Nat} (hst : st < 2) :
    (tcKind (softmaxKind d.site) = true → softmax (Work.n L) (Work.T L g) st d =
      tcS (Work.n L) (Work.T L g) st (14 * Work.n L * d.i + tcPos L d)) ∧
    (tcKind (softmaxKind d.site) = false → softmax (Work.n L) (Work.T L g) st d <
      tcS (Work.n L) (Work.T L g) st (14 * Work.n L * d.i + tcPos L d)) := by
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
  have hsl : ∀ lp, (lp = true → t + 1 < Work.n L) →
      softSlot ⟨site, i, t, w, m, l⟩ lp < Work.n L := fun lp h => softSlot_lt hn lp h
  cases site with
  | setMaxReg | bar0 =>
    obtain ⟨rfl, rfl⟩ := hstart (by simp)
    simp only [softmax, tcPos, softmaxKind, tcKind, Nat.mul_zero, Nat.add_zero]
    refine ⟨by simp, fun _ => ?_⟩
    unfold tcS
    split_ifs
    · simp only [bandS, span, regT, bar0T, base]; omega
    · exact Progress.Time.fixed_lt (by decide)
  | statsW w =>
    rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
    · have hiT := hitem rfl
      simp only [softmax, tcPos, softmaxKind, tcKind]
      refine ⟨by simp, fun _ => ?_⟩
      exact at_lt (p := 0) (τ := 0) hiT hn (by decide) (by simp [tcOff])
    · have hiT := hitem rfl
      simp only [softmax, tcPos, softmaxKind, tcKind]
      refine ⟨by simp, fun _ => ?_⟩
      by_cases h1 : 1 < Work.n L
      · exact at_lt (p := 0) (τ := 1) hiT h1 (by decide) (by simp [tcOff])
      · have h1' : Work.n L = 1 := by omega
        rw [h1']
        exact next_item (by decide) hiT le_rfl (hb _ (by decide))
    · have hiT := hitem rfl
      have ht := htrip rfl
      simp only [softmax, tcPos, softmaxKind, tcKind]
      refine ⟨by simp, fun _ => ?_⟩
      by_cases h1 : t + 2 < Work.n L
      · exact at_lt (p := 0) hiT h1 (by decide) (by simp [tcOff])
      · rw [show 14 * (t + 2) = 14 * Work.n L by omega]
        exact next_item hn hiT (by omega) (hb _ (by decide))
    · obtain ⟨rfl, rfl⟩ := htail (by simp)
      simp only [softmax, tcPos, softmaxKind, tcKind, Nat.add_zero, tcS_tail]
      exact ⟨by simp, fun _ => Progress.Time.tail_lt (by simp only [bandS]; omega)⟩
  | sW lp =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨by simp, fun _ => ?_⟩
    exact at_lt (p := 0) (hitem rfl) (hsl lp fun h => htrip (by subst h; rfl)) (by decide)
      (by simp [tcOff])
  | ld lp c =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨fun _ => ?_, by simp⟩
    exact at_eq (hitem rfl) (hsl lp fun h => htrip (by subst h; rfl)) (by omega)
      (by unfold tcOff; split_ifs <;> omega)
  | ldW lp c =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨fun _ => ?_, by simp⟩
    rw [show 14 * softSlot ⟨.ldW lp c, i, t, w, m, l⟩ lp + 2 * c.val + 1 =
      14 * softSlot ⟨.ldW lp c, i, t, w, m, l⟩ lp + (2 * c.val + 1) by ring]
    exact at_eq (hitem rfl) (hsl lp fun h => htrip (by subst h; rfl)) (by omega)
      (by unfold tcOff; split_ifs <;> omega)
  | alphaSt =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨by simp, fun _ => ?_⟩
    exact at_lt (hitem rfl) (htrip rfl) (by decide) (by simp [tcOff])
  | gen j =>
    rcases Softmax.fin3_cases j with rfl | rfl | rfl
    · simp only [softmax, tcPos, softmaxKind, tcKind]
      refine ⟨by simp, fun _ => ?_⟩
      exact at_lt (τ := 0) (p := 8) (hitem rfl) hn (by decide) (by simp [tcOff])
    · simp only [softmax, tcPos, softmaxKind, tcKind]
      refine ⟨by simp, fun _ => ?_⟩
      exact at_lt (hitem rfl) (htrip rfl) (by decide) (by simp [tcOff])
    · simp only [softmax, tcPos, softmaxKind, tcKind, hN]
      refine ⟨by simp, fun _ => ?_⟩
      exact next_item hn (hitem rfl) le_rfl (hb _ (by decide))
  | lSt =>
    simp only [softmax, tcPos, softmaxKind, tcKind, hN]
    refine ⟨by simp, fun _ => ?_⟩
    exact next_item hn (hitem rfl) le_rfl (hb _ (by decide))
  | pst lp c =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨fun _ => ?_, by simp⟩
    exact at_eq (hitem rfl) (hsl lp fun h => htrip (by subst h; rfl)) (by split_ifs <;> omega)
      (by unfold tcOff; split_ifs <;> omega)
  | pwait lp h =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨fun _ => ?_, by simp⟩
    exact at_eq (hitem rfl) (hsl lp fun h => htrip (by subst h; rfl)) (by split_ifs <;> omega)
      (by have := h.isLt; unfold tcOff; split_ifs <;> omega)
  | pArr lp =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨by simp, fun _ => ?_⟩
    exact at_lt (hitem rfl) (hsl lp fun h => htrip (by subst h; rfl)) (by decide)
      (by simp [tcOff])
  | warpBar lp | el lp | p2Arr lp =>
    simp only [softmax, tcPos, softmaxKind, tcKind]
    refine ⟨by simp, fun _ => ?_⟩
    exact next_tile (hitem rfl) (hsl lp fun h => htrip (by subst h; rfl)) (hb _ (by decide))
  | barEnd | exit =>
    obtain ⟨rfl, rfl⟩ := htail (by simp)
    simp only [softmax, tcPos, softmaxKind, tcKind, Nat.add_zero, tcS_tail]
    exact ⟨by simp, fun _ => Progress.Time.tail_lt (by omega)⟩

end Soft
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
