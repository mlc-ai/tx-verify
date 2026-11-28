-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TcCmp

@[expose] public section

/-! # Comparing warpgroup 0's places with a state at the vote

For `d` at the vote site and `s` a state of a lane of the same CTA that has made at most `d`'s
votes and is not at the vote with as many, `s` is at an earlier place (`vote_place_lt`): before
the vote in the same block (the sites of order below 38), or in an earlier block, or in the
set-up. A state at the vote has made fewer votes than the CTA's blocks (`vote_lt_rounds`), a state
at the exit exactly as many (`vOrd_exit`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {L : Launch} {g g' : Nat}

/-- A state of the loop is block `r`'s, `r` below the block count. -/
theorem loop_form {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) (hk : d.site.reg = .loop) :
    ∃ r, r < rounds d.l0 d.l1 ∧ d.bi.toNat = r + 1 := by
  simp only [RefCore, hk, RefAt, Control.D.words] at hJ
  obtain ⟨r, hl, -⟩ := hJ
  obtain ⟨-, hR, hr, hbi, -⟩ := hl
  dsimp only at hR hr hbi
  exact ⟨r, hr, by rw [hbi]; exact toNat_W (by omega)⟩

/-- **A state at the vote has made fewer votes than there are blocks.** -/
theorem vote_lt_rounds {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) (hd : d.site = .vote) :
    vOrd d < rounds d.l0 d.l1 := by
  obtain ⟨r, hr, hb⟩ := loop_form hJ (by rw [hd]; rfl)
  simp only [vOrd, hd, Site.reg, Site.ord, hb, Nat.lt_irrefl, ite_false]
  omega

/-- **A state at the exit has made one vote per block.** -/
theorem vOrd_exit {d : D} (hd : d.site = .exit) : vOrd d = rounds d.l0 d.l1 := by
  simp [vOrd, hd, Site.reg]

/-- A site of the loop before the vote, at an order up to the vote's, is at an order below it. -/
theorem oo_pre_vote {d : D} (hk : d.site.reg = .loop) (ho : d.site.ord ≤ 38)
    (hv : d.site ≠ .vote) : d.site.ord + elOff d < 38 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [Site.reg, Site.ord, elOff, reduceCtorEq, ne_eq, not_true_eq_false,
    w0Wv, w0Wq, w0ArrV, w0ArrS] at hk ho hv ⊢ <;>
    (try have := ‹Fin _›.isLt) <;> omega

/-- **A lane no later than a vote state with as many votes is earlier**: the state `s` has made at
most `d`'s votes, and it is not at a vote with as many. -/
theorem vote_place_lt {d s : D} {n : Cnt → Nat} {n' : Cnt → Nat} (hJd : RefCore L g d n)
    (hJs : RefCore L g' s n') (hd : d.site = .vote)
    (hR : s.site.reg ≠ .setup → rounds s.l0 s.l1 = rounds d.l0 d.l1)
    (hv : vOrd s ≤ vOrd d) (hne : ¬ (vOrd s = vOrd d ∧ s.site = .vote)) :
    place s < place d := by
  obtain ⟨r, hr, hb⟩ := loop_form hJd (by rw [hd]; rfl)
  have hpd : place d = wg0Blk0 + stride * r + 38 := by
    have hx : d.site ≠ .ebar ∧ d.site ≠ .dealloc ∧ d.site ≠ .exit := by
      rw [hd]; simp
    rw [place_reg hx]
    simp only [regPlace, hd, Site.reg, Site.ord, elOff, hb, Nat.add_sub_cancel]
  have hvd : vOrd d = r := by
    simp only [vOrd, hd, Site.reg, Site.ord, hb, Nat.lt_irrefl, ite_false]; omega
  have he := elOff_le s
  have hx : s.site.reg ≠ .loop → s.site.reg ≠ .setup → False := by
    intro h1 h2
    have := hR h2
    have h3 : vOrd s = rounds s.l0 s.l1 := by
      unfold vOrd; split <;> simp_all
    omega
  by_cases hs0 : s.site.reg = .setup
  · have hxs : s.site ≠ .ebar ∧ s.site ≠ .dealloc ∧ s.site ≠ .exit := by
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp [h, Site.reg] at hs0
    rw [place_reg hxs, hs0, regPlace, hpd]
    have := (setup_tab _ hs0).1
    simp only [wg0Blk0, loopBase, wg0Off, wg0Org, stride]
    omega
  by_cases hs1 : s.site.reg = .loop
  · obtain ⟨r', hr', hb'⟩ := loop_form hJs hs1
    have hxs : s.site ≠ .ebar ∧ s.site ≠ .dealloc ∧ s.site ≠ .exit := by
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp [h, Site.reg] at hs1
    rw [place_reg hxs, hs1, regPlace, hpd]
    have hvs : vOrd s = r' + (if 38 < s.site.ord then 1 else 0) := by
      simp only [vOrd, hs1, hb']; omega
    have hlt := ord_loop_le s.site hs1
    simp only [hb', Nat.add_sub_cancel]
    by_cases hc : r' < r
    · have : stride * r' + stride ≤ stride * r := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hc
      simp only [stride] at this ⊢
      omega
    · have hrr : r' = r := by
        split_ifs at hvs <;> omega
      subst hrr
      have ho : s.site.ord ≤ 38 := by split_ifs at hvs <;> omega
      have hsv : s.site ≠ .vote := fun h => hne ⟨by omega, h⟩
      have := oo_pre_vote hs1 ho hsv
      omega
  · exact (hx hs1 hs0).elim

set_option maxRecDepth 100000 in
/-- **The only site at pc 578 is the vote.** -/
theorem site_vote_of_pc {s : Site} (h : s.pc = 578) : s = .vote := by
  revert h
  cases s <;> first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
