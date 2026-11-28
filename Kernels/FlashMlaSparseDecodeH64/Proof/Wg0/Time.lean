-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefArith
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots

@[expose] public section

/-! # Warpgroup 0's local time

The role's states in the order of its events (`place`), on the one table of `Lib/Slots.lean`:

* the set-up's sites densely at `0`–`5` (`smr`, `sink`, `lenA`, `lenB`, `bwait`, `arrL`: the
  arrival on `last_store_done` at `w0ArrL = 5`, glued `lastArr = 105`);
* block `r` (read off `bi = r + 1`) at `wg0Blk0 + stride * r + ord + el` (`Site.ord`: barrier 9 at
  `0`, the polls of `valid_coord_ready` and `qk_done` at `w0Wv`, `w0Wq`, the arrival on
  `valid_coord_free` at `w0ArrV`, the arrival on `so_ready` at `w0ArrS`; an element of a vector
  access adds its index, `elOff`);
* the epilogue after `R` blocks at `wg0EpiBlk0 + stride * R + ord + el` (the poll of `sv_done` at
  `w0Wsv`; each output chunk takes 38 places);
* barrier 12 at `endPlace` (glued `endSlot`), the deallocation and the return after it.

The glued table (`Common/Time.lean`) places the role at `roleBase = wg0Org`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {L : Launch} {g : Nat}

/-- An output chunk's first place in the epilogue. -/
def chunkBase (c : Fin 4) : Nat := 7 + 38 * c.val

/-- A site's place in its region: the set-up's order, its block's, the epilogue's. -/
def Site.ord : Site → Nat
  | .smr => 0 | .sink => 1 | .lenA => 2 | .lenB => 3 | .bwait => 4 | .arrL => w0ArrL
  | .bar0 => 0 | .wv => w0Wv | .wq => w0Wq | .tcfa => 3 | .sld _ k => 4 + k.val | .sldw => 6
  | .tcfb => 7 | .vm => 8 | .pst k => 9 + k.val | .bar1 => 17 | .pld k => 18 + 2 * k.val
  | .mst => 34 | .bar2 => 35 | .arrV => w0ArrV | .mld => 37 | .vote => 38
  | .ost k => 39 + 4 * k.val | .rsf => 55
  | .rld c => 56 + 4 * c.val | .rldw c => 57 + 4 * c.val | .rst c => 58 + 4 * c.val
  | .rstw c => 59 + 4 * c.val | .rsfb => 72 | .fpx => 73 | .arrS => w0ArrS
  | .ebar0 => 0 | .est => 1 | .ebar1 => 2 | .eld => 3 | .lse => 4 | .wsv => w0Wsv | .efa => 6
  | .old c => chunkBase c | .oldw c => chunkBase c + 1 | .ost2 c k => chunkBase c + 2 + 4 * k.val
  | .ofpx c => chunkBase c + 34 | .obar c => chunkBase c + 35 | .oel c => chunkBase c + 36
  | .otma c => chunkBase c + 37 | .commit => 159
  | .ebar | .dealloc | .exit => 0

/-- The element of a vector access read so far (`pld`: at most `1`; `ost`, `ost2`: at most
`3`); `0` elsewhere. -/
def elOff (d : D) : Nat :=
  match d.site with
  | .pld _ => min d.el 1
  | .ost _ | .ost2 _ _ => min d.el 3
  | _ => 0

/-- The local place of barrier 12: glued `endSlot`. -/
def endPlace : Nat := endSlot - wg0Org

/-- The place of a state of region `k` at site order `o`. -/
def regPlace (d : D) : Reg → Nat
  | .setup => d.site.ord
  | .loop => wg0Blk0 + stride * (d.bi.toNat - 1) + d.site.ord + elOff d
  | .epi => wg0EpiBlk0 + stride * rounds d.l0 d.l1 + d.site.ord + elOff d
  | .fin => endPlace

/-- **The place of a state** in the role's order. -/
def place (d : D) : Nat :=
  match d.site with
  | .ebar => endPlace
  | .dealloc => endPlace + 1
  | .exit => endPlace + 2
  | s => regPlace d s.reg

/-- **The local time of a state**: its place. -/
def time (d : D) : Nat := place d

/-- The largest place: the return. -/
def top : Nat := endPlace + 2

/-- The block count is below `2 ^ 26`. -/
theorem rounds_lt (l0 l1 : BitVec 64) : rounds l0 l1 < 2 ^ 26 := by
  cases h : scmpi .lt .s (r15 l0 l1) 64
  · exact (rounds_range h).2.1
  · simp [rounds, h]

theorem ord_loop_le (s : Site) (h : s.reg = .loop) : s.ord + 3 ≤ 77 := by
  cases s <;> simp only [Site.reg, reduceCtorEq] at h <;>
    simp only [Site.ord, w0Wv, w0Wq, w0ArrV, w0ArrS] <;> (try have := ‹Fin _›.isLt) <;> omega

theorem ord_epi_le (s : Site) : s.ord ≤ 159 := by
  cases s <;> simp only [Site.ord, chunkBase, w0ArrL, w0Wv, w0Wq, w0ArrV, w0ArrS, w0Wsv] <;>
    (try have := ‹Fin _›.isLt) <;> (try have := ‹Fin 4›.isLt) <;> omega

theorem elOff_le (d : D) : elOff d ≤ 3 := by
  unfold elOff; split <;> omega

/-- Off barrier 12 and after, the place is the region's. -/
theorem place_reg {d : D} (h : d.site ≠ .ebar ∧ d.site ≠ .dealloc ∧ d.site ≠ .exit) :
    place d = regPlace d d.site.reg := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold place
  split <;> simp_all

/-- **Every place is at most `top`** at a state with the reference invariant. -/
theorem place_le {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) : place d ≤ top := by
  have hR := rounds_lt d.l0 d.l1
  have he := elOff_le d
  have ho := ord_epi_le d.site
  unfold RefCore at hJ
  by_cases hx : d.site = .ebar ∨ d.site = .dealloc ∨ d.site = .exit
  · rcases hx with hx | hx | hx <;> simp [place, top, hx]
  · rw [place_reg (by tauto)]
    unfold top
    cases hk : d.site.reg <;> simp only [regPlace]
    · simp only [endPlace, endSlot, wg0Org, loopBase, stride, blockCap]
      omega
    · rw [hk] at hJ
      obtain ⟨r, ⟨-, hR', hr, hbi, -⟩, -⟩ := hJ
      simp only [Control.D.words] at hbi hr
      rw [hbi, toNat_W (by omega)]
      have := ord_loop_le d.site hk
      simp only [endPlace, endSlot, wg0Org, loopBase, stride, blockCap, wg0Blk0, wg0Off]
      omega
    · simp only [endPlace, endSlot, wg0Org, loopBase, stride, blockCap, wg0EpiBlk0, w0Epi]
      omega
    · omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
