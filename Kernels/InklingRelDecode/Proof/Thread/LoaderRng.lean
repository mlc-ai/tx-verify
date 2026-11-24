-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderRing

@[expose] public section

/-! # The counter bounds along the loader's steps

`Rng` (the counters below `2 ^ 31` from the second load on, the counter below `num_iters` in the
loop) is not an invariant of the machine, which follows every loaded word. It is kept by every step
but the two loads (`Rng.next`); the two loads give it when the words they load read as numbers
below `2 ^ 31` (`Rng.of_readI`, `Rng.of_readN`). Below `2 ^ 31` the signed entry test is the
natural one and the increment does not wrap. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

theorem sxI_of_lt {i : Nat} (hi : i < 2 ^ 31) : sxI i = (i : Int) := by
  unfold sxI
  have h1 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
  rw [h1, ite_eq_left (show i < 2 ^ 31 from hi)]

/-- **The counter bounds after a step** other than the two loads. -/
theorem Rng.next {d d' : D} {e : Event} (hr : Rng d) (h0 : d.site ≠ .ld0)
    (h1 : d.site ≠ .ld1) (hn : Loader.next L g d e = some (some d')) : Rng d' := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  obtain ⟨hI, hN, hL, hWi, hWn⟩ := hr
  simp only [wordI, wordN] at hI hN hL h0 h1 hWi hWn
  cases s
  case ld0 => exact absurd rfl h0
  case ld1 => exact absurd rfl h1
  case bar0 =>
    have hi := hI rfl
    have hn' := hN rfl
    simp only [Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs with hc
      · exact ⟨fun h => by simp [Site.iBounded, Site.bounded, Site.inLoop] at h,
          fun h => by simp [Site.bounded, Site.inLoop] at h, fun h => by simp [Site.inLoop] at h,
          fun h => by simp [Site.iBounded, Site.bounded, Site.inLoop] at h,
          fun h => by simp [Site.bounded, Site.inLoop] at h⟩
      · rw [sxI_of_lt hi, sxI_of_lt hn'] at hc
        exact ⟨fun _ => hi, fun _ => hn', fun _ => by simp only; omega, fun _ => hWi rfl,
          fun _ => hWn rfl⟩
    · cases hn
  all_goals
    simp only [Loader.next, afterIter] at hn
    (repeat' split at hn)
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
      | (cases hn; done)
      | (simp only [Option.some.injEq] at hn
         subst hn
         first
           | exact ⟨hI, hN, hL, hWi, hWn⟩
           | (have hi := hI rfl
              have hn' := hN rfl
              have hl := hL rfl
              have hwn := hWn rfl
              have hm : (i + 1) % 2 ^ 32 = i + 1 := Nat.mod_eq_of_lt (by omega)
              refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
                simp only [Site.iBounded, Site.bounded, Site.inLoop, Bool.false_eq_true,
                  wordI, wordN, Function.update_self, Raw.word32Of_b32, hm,
                  Function.update_of_ne (show (467 : Nat) ≠ 1905 by decide)] at h ⊢ <;>
                omega))

/-- After an iteration the loader is at the next iteration's poll or at the exit barrier. -/
theorem afterIter_site (d : D) : (afterIter d).site = .bar1 ∨ (afterIter d).site = .wait := by
  simp only [afterIter]
  split
  · exact .inl rfl
  · exact .inr rfl

theorem afterIter_pro (d : D) :
    (afterIter d).pro = Function.update d.pro 1905 (b32 ((d.i + 1) % 2 ^ 32)) := by
  simp only [afterIter]
  split <;> rfl

/-- **A step keeps the inherited registers**, except the two loaded words. -/
theorem next_pro {d d' : D} {e : Event} (h : Loader.next L g d e = some (some d')) :
    ∀ r, r ≠ 1905 → r ≠ 467 → d'.pro r = d.pro r := by
  intro r h1 h2
  have key : d'.pro = d.pro ∨ d'.pro = Function.update d.pro 1905 (b32 ((d.i + 1) % 2 ^ 32)) ∨
      (∃ v, d'.pro = Function.update d.pro 1905 v) ∨
      (∃ v, d'.pro = Function.update d.pro 467 v) := by
    obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
    cases s <;> simp only [Loader.next] at h <;> (repeat' split at h) <;>
      simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first
        | exact .inl rfl
        | exact .inr (.inl (afterIter_pro _))
        | exact .inr (.inr (.inl ⟨_, rfl⟩))
        | exact .inr (.inr (.inr ⟨_, rfl⟩))
  rcases key with h' | h' | ⟨v, h'⟩ | ⟨v, h'⟩ <;> rw [h'] <;>
    simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-- **The first load** with a word that reads as a number below `2 ^ 31`. -/
theorem Rng.of_readI (d : D) {v : Value} {x : Nat} (hv : Raw.word32Of v = some x)
    (hx : x < 2 ^ 31) : Rng (readI d v) :=
  ⟨fun _ => by simp [readI, hv]; omega, fun h => by simp [readI, Site.bounded, Site.inLoop] at h,
    fun h => by simp [readI, Site.inLoop] at h, fun _ => by simp [readI, wordI, hv],
    fun h => by simp [readI, Site.bounded, Site.inLoop] at h⟩

/-- **The second load** with a word that reads as a number below `2 ^ 31`, after the first. -/
theorem Rng.of_readN {d : D} (hr : Rng d) (hs : d.site = .ld1) {v : Value} {x : Nat}
    (hv : Raw.word32Of v = some x) (hx : x < 2 ^ 31) : Rng (readN d v) :=
  ⟨fun _ => hr.bndI (by rw [hs]; rfl), fun _ => by simp [readN, hv]; omega,
    fun h => by simp [readN, Site.inLoop] at h,
    fun _ => by
      have := hr.wi (by rw [hs]; rfl)
      simpa [readN, wordI, Function.update_of_ne (show (1905 : Nat) ≠ 467 by decide)] using this,
    fun _ => by simp [readN, wordN, hv]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
