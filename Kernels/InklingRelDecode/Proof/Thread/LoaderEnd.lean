-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderStart

@[expose] public section

/-! # The loop's end

After the last copy pair (or the last election, for a lane that is not elected) the code adds one
iteration to its counters (`%r1444 += 1`, `%r1443 += 8`, `%r1442 += 32768`, `%r1441 += %r5`),
tests `num_iters != i + 1` and branches back to the ring-slot computation (`wait`) or falls
through to the exit barrier (`bar1`). The counter is a 32-bit word: the increment wraps from
`2 ^ 32 - 1` to `0`, and the closed forms of the table, modulo `2 ^ 32`, stay exact
(`loopEnd`, which `lw_pre` uses for the segments to `afterIter`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- The invariant of the state after an iteration. -/
theorem afterIter_inv (hi : Inv L g d) (hl : d.site.inLoop = true) :
    Inv L g (afterIter d) := by
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  obtain ⟨P, vi, vn, hP⟩ := hi.proW
  simp only at hP
  subst hP
  obtain ⟨hbi, hbn⟩ := hi.bits hl
  obtain ⟨hne, hlt⟩ := hi.loop hl
  simp only [wordI, wordN, Pro.valW, Nat.reduceEqDiff, ↓reduceIte] at hbi hbn hne hlt
  have hnl := Raw.word32Of_lt hbn
  obtain ⟨Q, hQ⟩ := hi.pro
  have hpro : ∀ r, r ≠ 1905 → r ≠ 467 →
      Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn r = Pro.val L g Q r := fun r h1 h2 => by
    have := hQ r h1 h2
    simp only [Pro.valW, h1, h2, ↓reduceIte] at this ⊢
    exact this
  rw [afterIter_valW]
  split_ifs with h
  · exact ⟨⟨Q, hpro⟩, fun h => by (rcases h with h | h <;> cases h),
      fun h => by simp [Site.bounded, Site.inLoop] at h, fun h => by simp [Site.inLoop] at h,
      fun h => by simp [Site.inLoop] at h, hi.ln, fun h => by cases h⟩
  · exact ⟨⟨Q, hpro⟩, fun h => by (rcases h with h | h <;> cases h),
      fun _ => by simp [wordN, Pro.valW, hbn],
      fun _ => ⟨by simp [wordI, Pro.valW, Raw.word32Of_b32], by simp [wordN, Pro.valW, hbn]⟩,
      fun _ => ⟨Ne.symm h, by simp only; omega⟩, hi.ln, fun h => by cases h⟩

theorem sub_afterIter (d : D) : sub (afterIter d) = 0 := by
  simp only [afterIter]
  split <;> rfl

theorem acc_afterIter (d : D) : acc (afterIter d) = [] := by
  simp only [afterIter]
  split <;> rfl

/-- The facts after a write of `x` to `r`, for a state whose table agrees with the old one's
except at `r`. -/
theorem holds_set_val {R : Nat → Option Value} {l1 l2 : List Nat} {val val' : Nat → Value}
    {r : Nat} {x : Value} (h : Holds R (factsFrom l1 val)) (hx : val' r = x)
    (hv : ∀ q ∈ l2, q ≠ r → val' q = val q ∧ q ∈ l1) :
    Holds (Function.update R r (some x)) (factsFrom l2 val') := by
  refine holds_of_pointwise fun q hq => ?_
  by_cases hd : q = r
  · subst hd
    simp [hx]
  · rw [Function.update_of_ne hd, (hv q hq hd).1]
    exact holds_mem h (mem_factsFrom (hv q hq hd).2)

/-- The three increments after the counter's (pcs 2414 to 2416). -/
theorem seg_incs (P : Pro) (vi vn : Value) (s : Site) (i n p0 p1 : Nat) (ln : Bool) :
    Seg kernel asms L g 3 2414
      (factsAt L g 2414 ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) 2417
      (factsAt L g 2417 ⟨s, Pro.valW L g P vi vn, i + 1, n, p0, p1, ln⟩) :=
  fun t h => by lw_seg h [Nat.mul_add, Nat.mul_one]

/-- **The loop's end**: from the instruction after the last copy of an iteration, the counters are
incremented (the counter register as a 32-bit word), and the loop branches back to the poll of the
next slot, or leaves for the exit barrier. -/
theorem loopEnd (P : Pro) (s : Site) (vi vn : Value) (i n p0 p1 : Nat) (ln : Bool)
    (hwi : Raw.word32Of vi = some (i % 2 ^ 32)) (hwn : Raw.word32Of vn = some n) :
    SegTo L g 2413 (factsAt L g 2413 ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩)
      (afterIter ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) := by
  rw [afterIter_valW]
  have hm : (i % 2 ^ 32 + 1) % 2 ^ 32 = (i + 1) % 2 ^ 32 := by omega
  have hA : Seg kernel asms L g 1 2413
      (factsAt L g 2413 ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩) 2414
      (factsAt L g 2414 ⟨s, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i, n, p0, p1, ln⟩) := by
    refine seg_inc (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit,
      Pro.valW])) hwi (fun R hR => ?_)
    rw [hm]
    have ht : table L g ⟨s, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i, n, p0, p1, ln⟩ =
        table L g ⟨s, Pro.valW L g P vi vn, i, n, p0, p1, ln⟩ := by
      simp [table, Pro.valW]
    refine holds_set_val hR (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW])
      fun q hq hne => ⟨?_, ?_⟩
    · unfold valueOf
      rw [ht]
      by_cases h2 : q = 467
      · subst h2; simp [Pro.valW]
      · simp [Pro.valW, hne, h2]
    · revert q; decide +kernel
  have hB := seg_incs (L := L) (g := g) P (b32 ((i + 1) % 2 ^ 32)) vn s i n p0 p1 ln
  have hil' : (i + 1) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hC : Seg kernel asms L g 1 2417
      (factsAt L g 2417 ⟨s, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i + 1, n, p0, p1, ln⟩)
      2418
      (factsAt L g 2418 ⟨s, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i + 1, n, p0, p1, ln⟩) :=
    seg_p25 (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW]))
      (tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit, Pro.valW])) hwn hil'
      (fun R hR => Raw.holds_set_live hR (by simp [valueOf, table, PTX.Flow.lookupLit])
        (by live_dec))
  have hmem : (25, Value.pred (decide (n ≠ (i + 1) % 2 ^ 32))) ∈
      factsAt L g 2418 ⟨s, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i + 1, n, p0, p1, ln⟩ :=
    tbl_mem (by live_dec) (by simp [valueOf, table, PTX.Flow.lookupLit])
  have hw' : Raw.word32Of (b32 ((i + 1) % 2 ^ 32)) = some ((i + 1) % 2 ^ 32) := by
    rw [Raw.word32Of_b32, Nat.mod_mod]
  obtain ⟨k, hD⟩ := segTo_bra (L := L) (g := g) (pc := 2418) (p := 25)
    (c := decide (n ≠ (i + 1) % 2 ^ 32))
    (d1 := ⟨.wait, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i + 1, n, p0, p1, ln⟩)
    (d2 := ⟨.bar1, Pro.valW L g P (b32 ((i + 1) % 2 ^ 32)) vn, i + 1, n, p0, p1, ln⟩)
    Flow.code_2418 hmem
    (fun _ => seg_head P (b32 ((i + 1) % 2 ^ 32)) vn (i + 1) n p0 p1 ln (pc0 := 2418) hw'
      (by live_dec) (by live_dec) s)
    (fun _ => segTo_here rfl rfl (by live_dec))
  by_cases hne : n = (i + 1) % 2 ^ 32
  · have hc : decide (n ≠ (i + 1) % 2 ^ 32) = false := decide_eq_false (by simpa using hne)
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hD
    rw [ite_eq_left hne]
    exact ⟨1 + (3 + (1 + k)), Seg.comp hA (Seg.comp hB (Seg.comp hC hD))⟩
  · have hc : decide (n ≠ (i + 1) % 2 ^ 32) = true := decide_eq_true hne
    simp only [hc, ↓reduceIte] at hD
    rw [ite_eq_right hne]
    exact ⟨1 + (3 + (1 + k)), Seg.comp hA (Seg.comp hB (Seg.comp hC hD))⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
