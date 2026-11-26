-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Cnt9
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region

@[expose] public section

/-! # Warpgroup 0's row-maximum exchange between barrier 9's events

The bytes of `rowMax` (`221184 + 4 t`, thread `t` of the warpgroup) are written at pcs 566 and
1155 (`mst`, `est`) and read at 572 and 1157 (`mld`, `eld`) only (`wg0_rmaxUse`). Block `r`'s
`mst` is after `2 r + 1` and its `mld` after `2 r + 2` of the lane's barrier-9 events (the
epilogue's `est`, `eld` likewise with `r = R`, the CTA's block count): between the two lies the
block's last barrier 9, so the parity of the count tells a store from a load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem rmax_site {s : Wg0.Site}
    (h : s.pc = 566 ∨ s.pc = 572 ∨ s.pc = 1155 ∨ s.pc = 1157) :
    s = .mst ∨ s = .mld ∨ s = .est ∨ s = .eld := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **The barrier-9 count before an exchange site**: block `r`'s (`r ≤ R`) is `2 r + 1` at a
store and `2 r + 2` at a load. -/
private theorem rmax_cnt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {kd : Kind}
    (he : X.get (g, k) = some ⟨pc, kd⟩) (hub : ∀ f, kd ≠ .ub f) (hr : 103 ≤ pc ∧ pc < 1842)
    (hs : pc = 566 ∨ pc = 572 ∨ pc = 1155 ∨ pc = 1157) :
    ∃ r ≤ blocksOf P L (g / L.block), ((X.tr g).take k).countP (Execution.isBarId 9) =
      if pc = 566 ∨ pc = 1155 then 2 * r + 1 else 2 * r + 2 := by
  obtain ⟨d, hRf, ⟨hpc, -⟩, hw⟩ := wg0_at hp hX hFw he hub hr
  obtain ⟨hC, hL, -, ht⟩ := hRf (wg0_take_noUb hX he)
  have hB : w0BarCnt X g k = Wg0.barOrd d := ht
  rw [w0_idCnt hp hX hFw hw (le_refl 9) (by omega) k (noUbBefore_of_get hX he), hB]
  simp only at hpc
  have hsite := rmax_site (s := d.site) (by rw [← hpc]; exact hs)
  have hl2 : 2 ≤ d.site.lens := by rcases hsite with h | h | h | h <;> rw [h] <;> decide
  rcases hsite with h | h | h | h
  · obtain ⟨r, hrR, ho, -⟩ := barOrd_loop hC hL (by rw [h]; rfl) hl2
    rw [h] at hpc
    simp only [Wg0.Site.pc] at hpc
    simp only [h, Wg0.Site.bidx] at ho
    rw [ho, (w0Cnt9_site _ _ hrR).1]
    exact ⟨r, hrR.le, by simp [hpc]⟩
  · obtain ⟨r, hrR, ho, -⟩ := barOrd_loop hC hL (by rw [h]; rfl) hl2
    rw [h] at hpc
    simp only [Wg0.Site.pc] at hpc
    simp only [h, Wg0.Site.bidx] at ho
    rw [ho, (w0Cnt9_site _ _ hrR).2]
    exact ⟨r, hrR.le, by simp [hpc]⟩
  all_goals
    have hR := Wg0.rounds_blocks hL hl2
    have hk : d.site.reg = Wg0.Reg.epi := by rw [h]; rfl
    have ho : Wg0.barOrd d = 3 * blocksOf P L (g / L.block) + d.site.bidx := by
      simp only [Wg0.barOrd, hk, hR]
    rw [h] at hpc
    simp only [Wg0.Site.pc] at hpc
    simp only [h, Wg0.Site.bidx] at ho
    rw [ho, w0Cnt9_epi _ _ _ (by omega)]
    exact ⟨blocksOf P L (g / L.block), le_refl _, by simp [hpc]⟩

/-- **A warpgroup-0 access of a `rowMax` byte** is a store (pc 566, 1155) after `2 r + 1`
barrier-9 events of the lane or a load (572, 1157) after `2 r + 2` (`r` at most the CTA's block
count), not a barrier event; a store's thread is named by the byte. The access reports its pc. -/
theorem wg0_rmaxUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} {a : Acc} {w : Bool} {l : Loc}
    (he : X.get (g, k) = some e) (hat : Wg0At L g e.pc) (hi : X.Access (g, k) a w)
    (hc : a.Covers l) (hl : MemRow.LocIn L (g / L.block) .rowMax l) :
    warp L g < 4 ∧ Execution.isBarId 9 e = false ∧ ∃ r ≤ blocksOf P L (g / L.block),
      ((X.tr g).take k).countP (Execution.isBarId 9) = (if w then 2 * r + 1 else 2 * r + 2) ∧
      (w = true → g % L.block = (l.addr - L.sharedBase - 221184) / 4) ∧
      (if w then e.pc = 566 ∨ e.pc = 1155 else e.pc = 572 ∨ e.pc = 1157) := by
  have hg := Frame.lt_of_get hX he
  have ht := MemRow.wg0_tid hat.1
  have htx : (L.tidOf g).x = g % L.block := by rw [tidOf_x_eq hp, hp.block]
  obtain ⟨ev, hev, -, hm⟩ := access_event hi
  rw [he] at hev
  cases hev
  have hl0 := hl
  have hc0 := hc
  obtain ⟨hls, -, hl1, hl2⟩ := hl
  obtain ⟨hcs, -, hc1, hc2⟩ := hc
  simp only [Region.lo, Region.size] at hl1 hl2
  rcases hi with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
    rw [h'] at he <;> cases he <;>
    rcases memRow_wg0 hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, hrd⟩ |
      ⟨_, _, hk, hwr⟩ | ⟨_, _, hk, hlse | hst⟩ <;> cases hk
  · have hpc : pc = 572 ∨ pc = 1157 := by
      rcases hrd with ⟨-, v, hv, hl'⟩ | ⟨k', hk', el, hel, -, hl'⟩ | ⟨h572, hl'⟩
      · obtain ⟨hl', hsz⟩ := hl'
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc] at hc1 hc2
        omega
      · obtain ⟨hl', hsz⟩ := hl'
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc] at hc1 hc2
        omega
      · exact h572
    obtain ⟨r, hr, hcnt⟩ := rmax_cnt hp hX hFw h' (fun _ h => by cases h) hat.2 (by omega)
    refine ⟨hat.1, rfl, r, hr, ?_, (fun h => by cases h), ?_⟩
    · rw [hcnt]
      rcases hpc with rfl | rfl <;> simp
    · simpa using hpc
  · have hw2 : (pc = 566 ∨ pc = 1155) ∧
        g % L.block = (l.addr - L.sharedBase - 221184) / 4 := by
      rcases hwr with ⟨k', hk', -, hl'⟩ | ⟨h566, hl'⟩ | ⟨k', hk', el, hel, -, hl'⟩
      · have hx : (L.tidOf g).x / 32 ^^^ 2 < 4 :=
          Nat.xor_lt_two_pow (n := 2) (by omega) (by omega)
        obtain ⟨hl', hsz⟩ := hl'
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc] at hc1 hc2
        omega
      · obtain ⟨hl', hsz⟩ := hl'
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc] at hc1 hc2
        exact ⟨h566, by omega⟩
      · obtain ⟨hl', hsz⟩ := hl'
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc] at hc1 hc2
        omega
    obtain ⟨hpc, hidx⟩ := hw2
    obtain ⟨r, hr, hcnt⟩ := rmax_cnt hp hX hFw h' (fun _ h => by cases h) hat.2 (by omega)
    refine ⟨hat.1, rfl, r, hr, ?_, fun _ => hidx, ?_⟩
    · rw [hcnt]
      rcases hpc with rfl | rfl <;> simp
    · simpa using hpc
  · obtain ⟨-, hl', -⟩ := hlse
    have hcs' : l.space = a.loc.space := hcs
    rw [hl', hls] at hcs'
    cases hcs'
  · have := locIn_eq ((MemRow.wg0Stage_in hat.1 hst).locIn hc0) hl0
    cases this.2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
