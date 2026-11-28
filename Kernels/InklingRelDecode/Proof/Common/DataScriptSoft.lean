-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataScript

@[expose] public section

/-! # The Softmax and epilogue arms of a data warp's script -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Descent

/-- The collectives a Softmax site of round `i` follows. -/
def softCount (p i : Nat) (s : Softmax.Site) : Nat :=
  13 + 5 * p + Lib.shflBase i + Softmax.shflInRound s i

theorem soft_off (s : Softmax.Site) (h : s.isShuffle = false) : s.pc ∉ shufPcs := by
  cases s <;> first
    | (simp [Softmax.Site.isShuffle] at h; done)
    | (rename_i j; revert j; decide +kernel)
    | decide +kernel

theorem soft_warp_iff (s : Softmax.Site) : isWarpAt s.pc = s.isShuffle := by
  cases s <;> first
    | (rename_i j; revert j; decide +kernel)
    | decide +kernel

theorem soft_idx_in {i r : Nat} (h : (0 < i ∧ r < 9) ∨ (i = 0 ∧ r < 3)) :
    softRound (Lib.shflBase i + r) = i ∧ ds_softIdx (Lib.shflBase i + r) = r := by
  unfold Lib.shflBase softRound ds_softIdx; split_ifs <;> omega

theorem soft_idx_next {i r : Nat} (h : (0 < i ∧ r = 9) ∨ (i = 0 ∧ r = 3)) :
    softRound (Lib.shflBase i + r) = i + 1 ∧ ds_softIdx (Lib.shflBase i + r) = 0 := by
  unfold Lib.shflBase softRound ds_softIdx; split_ifs <;> omega

theorem cn_soft {p lim i r : Nat} (hm : Lib.shflBase i + r < Lib.shflBase lim) :
    dataCn p lim (13 + 5 * p + Lib.shflBase i + r) =
      some (softSite (Lib.shflBase i + r)).pc := by
  have e : 13 + 5 * p + Lib.shflBase i + r - (13 + 5 * p) = Lib.shflBase i + r := by omega
  have h1 : ¬ 13 + 5 * p + Lib.shflBase i + r ≤ 12 + 5 * p := by omega
  simp [dataCn, h1, e, hm]

/-- A Softmax shuffle site is the script's shuffle at its count. -/
theorem soft_site_eq {i : Nat} (s : Softmax.Site) (sh : s.isShuffle = true)
    (h : (s = .shfl4 ∨ s = .shfl5 ∨ s = .shfl6) ∨ 0 < i) :
    softSite (Lib.shflBase i + Softmax.shflInRound s i) = s ∧
      softRound (Lib.shflBase i + Softmax.shflInRound s i) = i := by
  have key : ∀ r, ((0 < i ∧ r < 9) ∨ (i = 0 ∧ r < 3)) →
      softSite (Lib.shflBase i + r) = [.shfl4, .shfl5, .shfl6, .shfl7, .shfl8, .shfl9, .shfl10,
        .shfl11, .shfl12].getD r .shfl4 := fun r hr => by
    have := (soft_idx_in hr).2
    change [Softmax.Site.shfl4, .shfl5, .shfl6, .shfl7, .shfl8, .shfl9, .shfl10, .shfl11,
      .shfl12].getD (ds_softIdx _) .shfl4 = _
    rw [this]
  by_cases hi : i = 0
  · subst hi
    rcases h with h | h
    · rcases h with rfl | rfl | rfl <;>
        exact ⟨by rw [key _ (Or.inr ⟨rfl, by decide⟩)]; rfl,
          (soft_idx_in (Or.inr ⟨rfl, by decide⟩)).1⟩
    · omega
  · have hi' : 0 < i := by omega
    cases s <;> simp only [Softmax.Site.isShuffle, Bool.false_eq_true] at sh <;>
      exact ⟨by rw [key _ (Or.inl ⟨hi', by simp [Softmax.shflInRound]⟩)]; rfl,
        (soft_idx_in (Or.inl ⟨hi', by simp [Softmax.shflInRound]⟩)).1⟩

private theorem shuf_info (s : Softmax.Site) (i : Nat) (sh : s.isShuffle = true)
    (prev : Softmax.needsPrevious s = true → 0 < i) :
    ((s = .shfl4 ∨ s = .shfl5 ∨ s = .shfl6) ∨ 0 < i) ∧ Softmax.shflInRound s i < 9 ∧
      (i = 0 → Softmax.shflInRound s i < 3) := by
  cases s <;> simp_all [Softmax.Site.isShuffle, Softmax.needsPrevious, Softmax.shflInRound] <;>
    omega

private theorem round_room {i lim r : Nat} (hi : i < lim) (hr : r < 9) (h0 : i = 0 → r < 3) :
    Lib.shflBase i + r < Lib.shflBase lim := by
  have : Lib.shflBase (i + 1) ≤ Lib.shflBase lim := by
    rcases Nat.lt_or_ge (i + 1) lim with h | h
    · exact Nat.le_of_lt (Lib.shflBase_lt h)
    · have : i + 1 = lim := by omega
      rw [this]
  unfold Lib.shflBase at *
  split_ifs at * <;> omega

/-- **A Softmax site is at a warp collective** exactly when the script has its pc at its
count. -/
theorem soft_at_iff {p lim i : Nat} (s : Softmax.Site) (hv : s.isShuffle = true → i < lim)
    (prev : Softmax.needsPrevious s = true → 0 < i) :
    isWarpAt s.pc = true ↔ dataCn p lim (softCount p i s) = some s.pc := by
  by_cases sh : s.isShuffle = true
  · have w : isWarpAt s.pc = true := by rw [soft_warp_iff]; exact sh
    refine ⟨fun _ => ?_, fun _ => w⟩
    obtain ⟨hi, r9, r3⟩ := shuf_info s i sh prev
    obtain ⟨e1, -⟩ := soft_site_eq s sh hi
    have := cn_soft (p := p) (lim := lim) (i := i) (round_room (hv sh) r9 r3)
    unfold softCount
    rw [this, e1]
  · have off : s.isShuffle = false := by simpa using sh
    have w : isWarpAt s.pc = false := by rw [soft_warp_iff]; exact off
    rw [w]
    constructor
    · intro h; cases h
    · intro h
      exact absurd (ds_cn_mem (by unfold softCount; omega) h) (soft_off s off)

theorem soft_slot_at {p lim i : Nat} (s : Softmax.Site) (hv : i < lim)
    (prev : Softmax.needsPrevious s = true → 0 < i) (h : isWarpAt s.pc = true) :
    dataSlot p lim (softCount p i s) = softClock s i := by
  have sh : s.isShuffle = true := by rw [← soft_warp_iff]; exact h
  obtain ⟨hi, r9, r3⟩ := shuf_info s i sh prev
  obtain ⟨e1, e2⟩ := soft_site_eq s sh hi
  have hm := round_room hv r9 r3
  have e : softCount p i s - (13 + 5 * p) = Lib.shflBase i + Softmax.shflInRound s i := by
    unfold softCount; omega
  have hs := ds_soft_clock (Lib.shflBase i + Softmax.shflInRound s i)
  rw [e1, e2] at hs
  rw [hs]
  have big : 12 + 5 * p < softCount p i s := by unfold softCount; omega
  rw [ds_slot_soft big (by rw [e]; exact hm), e, e2]

private theorem early_clock (s : Softmax.Site) (i : Nat)
    (h : s = .setMaxReg ∨ s = .bar0 ∨ (∃ j, s = .pre j)) : softClock s i < 1200 := by
  rcases h with rfl | rfl | ⟨j, rfl⟩ <;> simp [softClock, Lib.Slots.enter, Lib.Slots.reuse]
  omega

private theorem loop_clock (s : Softmax.Site) (i : Nat) (h1 : s ≠ .setMaxReg) (h2 : s ≠ .bar0)
    (h3 : ∀ j, s ≠ .pre j) (h4 : s ≠ .epilogue) :
    softClock s i = 1200 + 400 * i + s.position := by
  cases s <;> simp_all [softClock, Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride] <;>
    omega

private theorem loop_pos (s : Softmax.Site) (i : Nat) (h1 : s ≠ .setMaxReg) (h2 : s ≠ .bar0)
    (h3 : ∀ j, s ≠ .pre j) (h4 : s ≠ .epilogue) (hs : s.isShuffle = false)
    (h : (0 < i ∧ Softmax.shflInRound s i < 9) ∨ (i = 0 ∧ Softmax.shflInRound s i < 3)) :
    s.position < ds_posOf (Softmax.shflInRound s i) := by
  by_cases i0 : i = 0 <;> cases s <;>
    simp_all [Softmax.shflInRound, Softmax.Site.position, ds_posOf, Softmax.Site.isShuffle] <;>
    omega

theorem cn_some_of_le {p lim m n : Nat} (hm : 13 + 5 * p ≤ m) (hle : m ≤ n)
    (hn : (dataCn p lim n).isSome = true) : (dataCn p lim m).isSome = true := by
  unfold dataCn at hn ⊢
  have h0 : ¬ m = 0 := by omega
  have h1 : ¬ m ≤ 12 + 5 * p := by omega
  have h2 : ¬ n = 0 := by omega
  have h3 : ¬ n ≤ 12 + 5 * p := by omega
  simp only [h0, h1, h2, h3, ite_false] at hn ⊢
  split_ifs at hn ⊢ <;> first | rfl | omega

private theorem r_cases (s : Softmax.Site) (i : Nat)
    (pv : Softmax.needsPrevious s = true → 0 < i) :
    (0 < i ∧ Softmax.shflInRound s i < 9) ∨ (i = 0 ∧ Softmax.shflInRound s i < 3) ∨
    (0 < i ∧ Softmax.shflInRound s i = 9) ∨ (i = 0 ∧ Softmax.shflInRound s i = 3) := by
  by_cases i0 : i = 0
  · subst i0; cases s <;> simp_all [Softmax.shflInRound, Softmax.needsPrevious]
  · have : 0 < i := by omega
    cases s <;> simp [Softmax.shflInRound, i0, this]

private theorem not_early (s : Softmax.Site) : (s = .setMaxReg ∨ s = .bar0 ∨ (∃ j, s = .pre j)) ∨
    (s ≠ .setMaxReg ∧ s ≠ .bar0 ∧ (∀ j, s ≠ .pre j)) := by
  by_cases h : s = .setMaxReg ∨ s = .bar0 ∨ (∃ j, s = .pre j)
  · exact .inl h
  · right
    refine ⟨fun e => h (.inl e), fun e => h (.inr (.inl e)), fun j e => h (.inr (.inr ⟨j, e⟩))⟩

private theorem soft_here {p lim i : Nat} (hl : lim < 2 ^ 31) (s : Softmax.Site)
    (hv : (s ≠ .epilogue ∧ i < lim) ∨ (s = .epilogue ∧ i = lim)) (hs : s.isShuffle = false)
    (pv : Softmax.needsPrevious s = true → 0 < i)
    (hn : (dataCn p lim (softCount p i s)).isSome = true) :
    softClock s i < dataSlot p lim (softCount p i s) := by
  have big : 12 + 5 * p < softCount p i s := by unfold softCount; omega
  have e : softCount p i s - (13 + 5 * p) = Lib.shflBase i + Softmax.shflInRound s i := by
    unfold softCount; omega
  have fin := ds_finish_big
  have disj : Lib.shflBase i + Softmax.shflInRound s i < Lib.shflBase lim ∨
      (Lib.shflBase i + Softmax.shflInRound s i = Lib.shflBase lim ∧ lim ≠ 0) := by
    unfold dataCn at hn
    have h0 : ¬ softCount p i s = 0 := by omega
    have h1 : ¬ softCount p i s ≤ 12 + 5 * p := by omega
    simp only [h0, h1, ite_false, e] at hn
    split_ifs at hn with a b
    · exact .inl a
    · exact .inr b
    · simp at hn
  by_cases hepi : s = .epilogue
  · subst hepi
    have hi : i = lim := by rcases hv with ⟨h, -⟩ | ⟨-, h⟩ <;> [exact absurd rfl h; exact h]
    subst hi
    have r0 : Softmax.shflInRound .epilogue i = 0 := rfl
    have nA : ¬ softCount p i .epilogue - (13 + 5 * p) < Lib.shflBase i := by
      rw [e, r0]; omega
    rw [ds_slot_epi big nA]
    simp [softClock]
  · have hi : i < lim := by rcases hv with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; exact absurd h hepi]
    have i31 : i < 2 ^ 31 := by omega
    rcases not_early s with early | ⟨h1, h2, h3⟩
    · have c := early_clock s i early
      have : 1200 ≤ dataSlot p lim (softCount p i s) := by
        by_cases hA : softCount p i s - (13 + 5 * p) < Lib.shflBase lim
        · rw [ds_slot_soft big hA]; omega
        · rw [ds_slot_epi big hA]
          unfold Lib.Slots.finish Lib.Slots.frame Lib.Slots.stride; omega
      omega
    · have c := loop_clock s i h1 h2 h3 hepi
      have pb : s.position ≤ 90 := Softmax.position_bound s
      by_cases hA : softCount p i s - (13 + 5 * p) < Lib.shflBase lim
      · rw [ds_slot_soft big hA, e]
        have hb := ds_posOf_bound _ (ds_softIdx_lt (Lib.shflBase i + Softmax.shflInRound s i))
        rcases r_cases s i pv with h | h | h | h
        · obtain ⟨a, b⟩ := soft_idx_in (Or.inl ⟨h.1, h.2⟩)
          have := loop_pos s i h1 h2 h3 hepi hs (Or.inl h)
          rw [a, b]; omega
        · obtain ⟨a, b⟩ := soft_idx_in (Or.inr h)
          have := loop_pos s i h1 h2 h3 hepi hs (Or.inr h)
          rw [a, b]; omega
        · obtain ⟨a, b⟩ := soft_idx_next (Or.inl h)
          rw [a, b]; simp [ds_posOf]; omega
        · obtain ⟨a, b⟩ := soft_idx_next (Or.inr h)
          rw [a, b]; simp [ds_posOf]; omega
      · rw [ds_slot_epi big hA]
        omega

/-- A Softmax site that is no collective is earlier than every later slot. -/
theorem soft_slot_lt {p lim i n : Nat} (hp : p ≤ 3) (hl : lim < 2 ^ 31) (s : Softmax.Site)
    (hv : (s ≠ .epilogue ∧ i < lim) ∨ (s = .epilogue ∧ i = lim)) (hs : s.isShuffle = false)
    (pv : Softmax.needsPrevious s = true → 0 < i)
    (hn : (dataCn p lim n).isSome = true) (hle : softCount p i s ≤ n) :
    softClock s i < dataSlot p lim n := by
  have hc := cn_some_of_le (p := p) (lim := lim) (by unfold softCount; omega) hle hn
  have := soft_here hl s hv hs pv hc
  rcases Nat.eq_or_lt_of_le hle with rfl | h
  · exact this
  · have := data_slot_mono hp hl h hn
    omega

/-! ## The epilogue states -/

/-- The collectives before the epilogue's shuffle. -/
def epiBase (p lim : Nat) : Nat := 13 + 5 * p + Lib.shflBase lim

theorem epi_warp_iff (s : Epilogue.Site) : isWarpAt s.pc = decide (s = .shfl) := by
  cases s <;> first
    | (rename_i j; revert j; decide +kernel)
    | decide +kernel

theorem epi_off (s : Epilogue.Site) (h : s ≠ .shfl) : s.pc ∉ shufPcs := by
  cases s <;> first
    | exact absurd rfl h
    | (rename_i j; revert j; decide +kernel)
    | decide +kernel

theorem cn_epi {p lim : Nat} (h : lim ≠ 0) : dataCn p lim (epiBase p lim) = some 2603 := by
  have h1 : ¬ epiBase p lim ≤ 12 + 5 * p := by unfold epiBase; omega
  have h0 : ¬ epiBase p lim = 0 := by unfold epiBase; omega
  have e : epiBase p lim - (13 + 5 * p) = Lib.shflBase lim := by unfold epiBase; omega
  simp [dataCn, h0, h1, e, h]

theorem slot_epi_at {p lim : Nat} :
    dataSlot p lim (epiBase p lim) = Lib.Slots.finish + 4 := by
  have big : 12 + 5 * p < epiBase p lim := by unfold epiBase; omega
  have e : epiBase p lim - (13 + 5 * p) = Lib.shflBase lim := by unfold epiBase; omega
  exact ds_slot_epi big (by rw [e]; omega)

/-- **An epilogue site is at a warp collective** exactly when the script has its pc at its
count. -/
theorem epi_at_iff {p lim count : Nat} (s : Epilogue.Site) (hc : epiBase p lim ≤ count)
    (hs : s = .shfl → count = epiBase p lim ∧ lim ≠ 0) :
    isWarpAt s.pc = true ↔ dataCn p lim count = some s.pc := by
  rw [epi_warp_iff]
  by_cases sh : s = .shfl
  · subst sh
    obtain ⟨rfl, h⟩ := hs rfl
    simp [cn_epi h, Epilogue.Site.pc]
  · simp only [sh, decide_false, Bool.false_eq_true, false_iff]
    intro h
    exact epi_off s sh (ds_cn_mem (by unfold epiBase at hc; omega) h)

/-- The time of the epilogue's shuffle is its script slot. -/
theorem epi_slot_at {p lim : Nat} : dataSlot p lim (epiBase p lim) = epiClock .shfl := by
  rw [slot_epi_at, ds_epi_clock]

/-- An epilogue site that is no collective is earlier than the later slots. -/
theorem epi_slot_lt {p lim count n : Nat} (s : Epilogue.Site) (hc : epiBase p lim ≤ count)
    (hsh : s ≠ .shfl)
    (past : s ≠ .wait → lim ≠ 0 → epiBase p lim + 1 ≤ count)
    (hn : (dataCn p lim n).isSome = true) (hle : count ≤ n) :
    epiClock s < dataSlot p lim n := by
  have hn' : lim ≠ 0 ∧ n = epiBase p lim := by
    unfold dataCn at hn
    have h0 : ¬ n = 0 := by unfold epiBase at hc; omega
    have h1 : ¬ n ≤ 12 + 5 * p := by unfold epiBase at hc; omega
    simp only [h0, h1, ite_false] at hn
    split_ifs at hn with a b
    · unfold epiBase at hc; omega
    · unfold epiBase; omega
    · simp at hn
  obtain ⟨hl0, rfl⟩ := hn'
  have hw : s = .wait := by
    by_contra hw
    have := past hw hl0
    omega
  subst hw
  rw [slot_epi_at]
  simp [epiClock, Epilogue.Site.position]

end PTX.Kernels.InklingRelDecode.Proof
