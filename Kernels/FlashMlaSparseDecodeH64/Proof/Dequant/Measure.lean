-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Time
public import Lemmas.Kernel.FailCounts

@[expose] public section

/-! # Warpgroup 2's termination measure

The measure of a state is its place capped at `top` (`measure`, at most `top`). Every step the
machine follows from a state with the reference invariant stays (a failed poll) or moves to a
later place (`place_next`); under the reference invariant every place is at most `top`
(`place_le`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

attribute [local simp] deqBlk0 endPlace endSlot deqOrg loopBase deqOff stride blockCap

/-- The largest place: the exit. -/
def top : Nat := endPlace + 1

/-- **Warpgroup 2's measure.** -/
def measure (d : D) : Nat := min (place d) top

theorem measure_le (d : D) : measure d ≤ top := Nat.min_le_right _ _

/-- A lower bound of the place by the site: the set-up's order, `4` after it. -/
def Site.lo : Site → Nat
  | .smr => 0
  | .lenA => 1
  | .lenB => 2
  | .wq => 3
  | _ => 4

theorem place_ge (d : D) : d.site.lo ≤ place d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases s <;> simp only [place, Site.lo, deqBlk0, endPlace, endSlot, deqOrg, loopBase, deqOff,
    stride, blockCap] <;> omega

/-- **Every place is at most `top`** at a state with the reference invariant. -/
theorem place_le {d : D} {n : Cnt → Nat} (hJ : Ref L g d n) (h0 : n .ub = 0) : place d ≤ top := by
  have hR := rounds_lt d.l0 d.l1
  have hi := idx_le d.site
  have he := elOff_le d
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have hJ' := hJ h0
  unfold top
  cases s <;> simp only [place, deqBlk0, endPlace, endSlot, deqOrg, loopBase, deqOff, stride,
    blockCap] at hR hi he ⊢ <;> try omega
  all_goals
    obtain ⟨i, hw, -⟩ := hJ'
    have hb := blk_eq hw
    obtain ⟨hlt, -⟩ := hw
    simp only at hb hlt hR ⊢
    rw [hb]
    omega

/-- A step between loop states of the same block. -/
theorem body_lt {d d' : D} (h : d.site.inLoop = true) (h' : d'.site.inLoop = true)
    (hl : d'.l0 = d.l0 ∧ d'.l1 = d.l1 ∧ d'.cnt = d.cnt)
    (hlt : d.site.idx + elOff d < d'.site.idx + elOff d') : place d < place d' := by
  obtain ⟨h0, h1, hc⟩ := hl
  rw [place_loop h, place_loop h']
  have hb : blk d' = blk d := by simp only [blk, h0, h1, hc]
  rw [hb]
  omega

/-- A raw load's and a store's successor are later loop sites of the row (or the fence). -/
theorem rawNext_lt (r : Fin 4) (s : Fin 8) :
    (Site.raw r s).idx < (rawNext r s).idx ∧ (rawNext r s).inLoop = true := by
  fin_cases r <;> fin_cases s <;> decide

theorem storeNext_lt (r : Fin 4) (s : Fin 8) :
    (Site.store r s).idx < (storeNext r s).idx ∧ (storeNext r s).inLoop = true := by
  fin_cases r <;> fin_cases s <;> decide

set_option hygiene false in
/-- A step inside the block: the two places by `body_lt`. -/
local macro "body" : tactic => `(tactic| (
  refine .inr (body_lt rfl ?_ ⟨rfl, rfl, rfl⟩ ?_) <;>
    simp only [Site.idx, elOff, rawI, storeI, Site.inLoop] <;> omega))

/-- **Every step the machine follows** stays at a failed poll or moves to a later place. -/
theorem place_next {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : Ref L g d n) (h0 : n .ub = 0)
    (hn : succ P L g d e = some (some d')) : (d' = d ∧ e.counts = false) ∨ place d < place d' := by
  have hJ' := hJ h0
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases s with
  | smr =>
    have hge := place_ge d'
    simp only [succ, Option.some.injEq] at hn
    subst hn
    refine .inr (lt_of_lt_of_le ?_ hge)
    unfold afterSmr afterA
    split_ifs <;> simp [place, Site.lo]
  | lenA | lenB =>
    have hge := place_ge d'
    simp only [succ] at hn
    split at hn
    · unfold Code.ncNext at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        refine .inr (lt_of_lt_of_le ?_ hge)
        try unfold afterA
        try split_ifs
        all_goals simp [place, Site.lo]
      · simp at hn
      · simp at hn
    · simp at hn
  | wq =>
    simp only [succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs
      · refine .inr (lt_of_lt_of_le ?_ (place_ge _))
        unfold loopEntry
        split_ifs <;> simp [place, Site.lo]
      · exact .inl ⟨rfl, Event.counts_of_fail (by assumption) (by assumption)⟩
    · simp at hn
  | wraw | wsv =>
    simp only [succ, poll] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split_ifs
      · body
      · exact .inl ⟨rfl, Event.counts_of_fail (by assumption) (by assumption)⟩
    · simp at hn
  | scale r =>
    simp only [succ] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      unfold scaleNext
      split_ifs with hel
      · refine .inr (body_lt rfl rfl ⟨rfl, rfl, rfl⟩ ?_)
        simp only [Site.idx, elOff]
        simp only at hel
        omega
      · body
    · simp at hn
  | raw r s =>
    simp only [succ, dataRd] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      obtain ⟨h1, h2⟩ := rawNext_lt r s
      exact .inr (body_lt rfl h2 ⟨rfl, rfl, rfl⟩ (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)))
    · simp at hn
  | store r s =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    obtain ⟨h1, h2⟩ := storeNext_lt r s
    exact .inr (body_lt rfl h2 ⟨rfl, rfl, rfl⟩ (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)))
  | fpx | arrD =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    body
  | arrF =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    obtain ⟨i, hw, -⟩ := hJ'
    have hb := blk_eq hw
    obtain ⟨hi, hR, hcnt⟩ := hw
    obtain ⟨c1, c2⟩ := cnt_next hi hR
    simp only at hi hR hcnt hb
    refine .inr ?_
    rw [place_loop rfl, hb]
    simp only [Site.idx, elOff]
    dsimp only [advance]
    rw [hcnt, c2]
    split_ifs with hlast
    · rw [place_loop rfl]
      have hb' : blk ⟨.wraw, el, ac, l0, l1, addi (W ((2 ^ 32 - rounds l0 l1 + i) % 2 ^ 32)) 1,
          !sb, pb != sb⟩ = i + 1 :=
        blk_eq ⟨by dsimp only; simp at hlast; omega, hR, by simp only [c1]⟩
      rw [hb']
      simp only [Site.idx, elOff, stride]
      omega
    · simp only [place, deqBlk0, endPlace, endSlot, deqOrg, loopBase, deqOff, stride, blockCap]
      simp at hlast
      omega
  | bar =>
    simp only [succ, Option.some.injEq] at hn
    subst hn
    exact .inr (by simp only [place]; omega)
  | exit => simp [succ] at hn

/-- **The measure along a step** between states with the reference invariant (no undefined
behaviour): it never falls and a counted event raises it. -/
theorem measure_step {d d' : D} {n n' : Cnt → Nat} {e : Event} (hJ : Ref L g d n) (h0 : n .ub = 0)
    (hJ' : Ref L g d' n') (h0' : n' .ub = 0) (hn : succ P L g d e = some (some d')) :
    measure d ≤ measure d' ∧ (e.counts = true → measure d < measure d') := by
  have hle := place_le hJ' h0'
  rcases place_next hJ h0 hn with ⟨rfl, hc⟩ | hlt
  · exact ⟨Nat.le_refl _, fun h => by rw [hc] at h; cases h⟩
  · unfold measure
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
