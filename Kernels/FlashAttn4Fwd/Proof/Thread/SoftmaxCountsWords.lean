-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCounts

@[expose] public section

/-! # `Counts`: the words of a state

A step of the softmax machine is one of (`step_class`): a load of chunk `c` (the words of chunk
`c` become the load's values), the first tile's row maximum (the words become their selected
halves), a step to a state with no loaded chunk, or a step that keeps the words, the chunks, the
halving, the item and the tile. Each keeps `Counts.words` (`counts_step_words`): a load is the
thread's load of ordinal `4 (n i + T) + c` by its load count (`Counts.tcLd`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The classes of a step. -/
theorem step_class {L : Launch} {g : Nat} {d d' : D} {e : Event} (hi : Inv L g d)
    (hev : Ev L g d e) (hn : next L g d e = some (some d')) :
    (∃ lp c vals, d.site = .ld lp c ∧ e.kind = .tc (.ld (tmem L g (32 * c.val)) vals .s32x32b) ∧
      d'.site = .ldW lp c ∧ d'.w = loadW d.w c.val vals ∧ d'.i = d.i ∧ d'.t = d.t) ∨
    (d.site = .ldW false 3 ∧ d'.site = .gen 0 ∧ d'.w = half d.w ∧ d'.i = d.i ∧ d'.t = d.t) ∨
    chunks d' = 0 ∨
    (d'.w = d.w ∧ chunks d' = chunks d ∧ d'.site.halved = d.site.halved ∧ d'.i = d.i ∧
      tileNo d' = tileNo d) := by
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  rcases e with ⟨epc, ek⟩
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals first
    | exact .inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | exact .inr (.inl ⟨by trivial, rfl, rfl, rfl, rfl⟩)
    | exact .inr (.inr (.inl rfl))
    | exact .inr (.inr (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩))

/-- A load of a prefix is a load of a longer trace. -/
theorem LoadOrd.snoc {L : Launch} {g : Nat} {es : List Event} {e : Event} {o c : Nat}
    {vals : List Value} (h : LoadOrd L g es o c vals) : LoadOrd L g (es ++ [e]) o c vals := by
  obtain ⟨k, pc, hk, ho⟩ := h
  have hlt : k < es.length := (List.getElem?_eq_some_iff.mp hk).1
  refine ⟨k, pc, ?_, ?_⟩
  · rw [List.getElem?_append_left hlt]; exact hk
  · rw [List.take_append_of_le_length (by omega)]; exact ho

/-- The selected halves depend on the words of their pair only. -/
theorem half_congr {w w' : Nat → Value} (h : ∀ j < 128, w j = w' j) {k : Nat} (hk : k < 128) :
    half w k = half w' k := by
  unfold half
  split
  · rw [h k hk, h (k + 1) (by omega)]
  · rw [h (k - 1) (by omega), h k hk]

/-- The loads of the tile before a load site. -/
theorem ldPos_ld {d : D} {lp : Bool} {c : Fin 4} (hs : d.site = .ld lp c) :
    ldPos d = 4 * tileNo d + c.val := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  simp only at hs
  subst hs
  cases lp <;> simp [ldPos, Site.tile0, Site.inTrip]

set_option maxHeartbeats 1000000 in
/-- **`Counts.words` is kept by every step.** -/
theorem counts_step_words {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}
    (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hld : tcLdsIn (tmem L g 0) (tmem L g 128) es = 4 * trips L * d.i + ldPos d)
    (h : ∃ R : Nat → Value,
      (∀ c < chunks d, ∀ j < 32, ∃ vals,
        LoadOrd L g es (4 * (trips L * d.i + tileNo d) + c) c vals ∧
        R (32 * c + j) = vals.getD j (b32 0)) ∧
      ∀ k < 32 * chunks d, d.w k = if d.site.halved then half R k else R k) :
    ∃ R : Nat → Value,
      (∀ c < chunks d', ∀ j < 32, ∃ vals,
        LoadOrd L g (es ++ [e]) (4 * (trips L * d'.i + tileNo d') + c) c vals ∧
        R (32 * c + j) = vals.getD j (b32 0)) ∧
      ∀ k < 32 * chunks d', d'.w k = if d'.site.halved then half R k else R k := by
  obtain ⟨R, hR, hw⟩ := h
  rcases step_class hi hev hn with ⟨lp, c, vals, hs, hk, hs', hw', hi', ht'⟩ |
    ⟨hs, hs', hw', hi', ht'⟩ | h0 | ⟨hw', hc', hh', hi', hT'⟩
  · -- a load of chunk `c`
    have hT : tileNo d' = tileNo d := by
      simp only [tileNo, hs, hs', ht']
      cases lp <;> rfl
    have hc : chunks d = c.val := by simp [chunks, hs]
    have hc' : chunks d' = c.val + 1 := by simp [chunks, hs']
    have hh : d.site.halved = false := by rw [hs]; rfl
    have hh' : d'.site.halved = false := by rw [hs']; rfl
    refine ⟨fun k => if k / 32 = c.val then vals.getD (k % 32) (b32 0) else R k, ?_, ?_⟩
    · intro c' hc'' j hj
      rw [hc'] at hc''
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc'') with hlt | heq
      · obtain ⟨vs, ho, hr⟩ := hR c' (by omega) j hj
        refine ⟨vs, ?_, ?_⟩
        · rw [hi', hT]; exact ho.snoc
        · simp only [show (32 * c' + j) / 32 ≠ c.val by omega, ↓reduceIte]; exact hr
      · subst heq
        refine ⟨vals, ⟨es.length, e.pc, ?_, ?_⟩, ?_⟩
        · rw [List.getElem?_append_right (by omega), Nat.sub_self]
          obtain ⟨epc, ek⟩ := e
          simp only at hk
          subst hk
          rfl
        · rw [List.take_append_of_le_length (by omega), List.take_length, hi', hT]
          unfold tcLdsIn at hld
          rw [hld, ldPos_ld hs]
          ring
        · simp only [show (32 * c.val + j) / 32 = c.val by omega, ↓reduceIte,
            show (32 * c.val + j) % 32 = j by omega]
    · intro k hk'
      rw [hc'] at hk'
      rw [hw', hh']
      simp only [loadW, Bool.false_eq_true, ↓reduceIte]
      split
      · rfl
      · have := hw k (by rw [hc]; omega)
        rw [hh] at this
        simpa using this
  · -- the first tile's row maximum
    have hc : chunks d = 4 := by simp [chunks, hs]
    have hc' : chunks d' = 4 := by simp [chunks, hs']
    have hT : tileNo d' = tileNo d := by simp [tileNo, hs, hs', Site.tile0]
    have hh : d.site.halved = false := by rw [hs]; rfl
    have hh' : d'.site.halved = true := by rw [hs']; rfl
    refine ⟨R, fun c hc'' j hj => ?_, fun k hk => ?_⟩
    · obtain ⟨vs, ho, hr⟩ := hR c (by omega) j hj
      exact ⟨vs, by rw [hi', hT]; exact ho.snoc, hr⟩
    · rw [hc'] at hk
      simp only [hw', hh', ↓reduceIte]
      exact half_congr (fun j hj => by
        have := hw j (by rw [hc]; omega)
        rw [hh] at this
        simpa using this) (by omega)
  · -- no loaded chunk
    refine ⟨R, fun c hc => absurd hc (by omega), fun k hk => absurd hk (by omega)⟩
  · -- the words kept
    refine ⟨R, fun c hc j hj => ?_, fun k hk => ?_⟩
    · obtain ⟨vs, ho, hr⟩ := hR c (by omega) j hj
      exact ⟨vs, by rw [hi', hT']; exact ho.snoc, hr⟩
    · rw [hw', hh']
      exact hw k (by omega)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
