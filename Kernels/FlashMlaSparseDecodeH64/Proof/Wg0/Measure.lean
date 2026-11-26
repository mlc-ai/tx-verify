-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time
public import Lemmas.Kernel.FailCounts

@[expose] public section

/-! # Warpgroup 0's termination measure

The measure of a state is its place capped at `top` (`measure`, at most `top`). Every step the
machine follows from a state with the reference invariant stays (a failed poll) or moves to a
later place (`place_next`): inside a region the site order or the element grows; the set-up
enters block 0 or the epilogue; a block's end (`arrS`) enters the next block or the epilogue
(`place_arrS`, from the block words); the epilogue ends at barrier 12. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **Warpgroup 0's measure.** -/
def measure (d : D) : Nat := min (place d) top

theorem measure_le (d : D) : measure d ≤ top := Nat.min_le_right _ _

theorem i32_one : (i32 1).toNat = 1 := by decide

/-- **A block's end** moves to the next block's first place or the epilogue. -/
theorem place_arrS {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : RefCore L g d n)
    (hs : d.site = .arrS) (hn : succ P L g w d e = some (some d')) : place d < place d' := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hs
  subst hs
  unfold RefCore at hJ
  obtain ⟨r, ⟨-, hR, hr, hbi, -⟩, -⟩ := hJ
  simp only [Control.D.words] at hbi hR hr
  subst hbi
  have hb := bi_next (r := r) (by omega)
  simp only [succ, advance] at hn
  have h1 : (W (r + 1)).toNat = r + 1 := toNat_W (by omega)
  have h2 : (W (r + 1 + 1)).toNat = r + 1 + 1 := toNat_W (by omega)
  split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
    simp only [place, regPlace, Site.reg, Site.ord, elOff, h1, hb, h2, wg0Blk0, wg0EpiBlk0,
      loopBase, wg0Off, w0Epi, wg0Org, stride, w0ArrS] <;> omega

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **Every step the machine follows** stays at a failed poll or moves to a later place. -/
theorem place_next {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : RefCore L g d n)
    (hn : succ P L g w d e = some (some d')) :
    (d' = d ∧ e.counts = false) ∨ place d < place d' := by
  by_cases ha : d.site = .arrS
  · exact .inr (place_arrS hJ ha hn)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at ha
  have hR := rounds_lt l0 l1
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals first
    | exact absurd rfl ha
    | skip
  all_goals
    simp only [succ, dataRd, tcLoad, ncWord, poll, elemNext, afterSmr, afterSink, afterA,
      finish, afterOst, nextChunk, afterObar, afterEld, loopEntry, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Fin.zero_eta, Fin.mk_one] at hn
    repeat' split at hn
    all_goals (simp only [Option.some.injEq, reduceCtorEq] at hn) <;> subst hn <;>
      first
      | (refine .inl ⟨rfl, ?_⟩; exact Event.counts_of_fail (by assumption) (by assumption))
      | (right
         simp only [place, regPlace, Site.reg, Site.ord, elOff, chunkBase, i32_one, endPlace,
           endSlot, wg0Blk0, wg0EpiBlk0, loopBase, wg0Off, w0Epi, wg0Org, stride, blockCap,
           w0ArrL, w0Wv, w0Wq, w0ArrV, w0ArrS, w0Wsv, Fin.isValue, Fin.val_zero, Fin.val_one,
           Fin.val_two]
         omega)

/-- **The measure along a step** between states with the reference invariant: it never falls and
a counted event raises it. -/
theorem measure_step {d d' : D} {n n' : Cnt → Nat} {e : Event} (hJ : RefCore L g d n)
    (hJ' : RefCore L g d' n') (hn : succ P L g w d e = some (some d')) :
    measure d ≤ measure d' ∧ (e.counts = true → measure d < measure d') := by
  have hle := place_le hJ'
  rcases place_next hJ hn with ⟨rfl, hc⟩ | hlt
  · exact ⟨Nat.le_refl _, fun h => by rw [hc] at h; cases h⟩
  · unfold measure
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
