-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Sync9
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Rmax

@[expose] public section

/-! # The row-maximum exchange is ordered

The bytes of `rowMax` are accessed by threads of warpgroup 0 only (`region_thread`, the rows of
`access_region`): a store at pc 566 or 1155 after `2 r + 1` barrier-9 events of its lane, a load at
572 or 1157 after `2 r + 2` (`wg0_rmaxUse`), `r` at most the block count. The counts of a store
and a load differ in parity, so one is below the other, and barrier 9 orders the event after
fewer barrier-9 events before the other (`bar9_order`): the store before the load of the same
round (the block's last barrier 9 between them) and the load before the next round's store.
Two stores of a byte are one thread's (the byte names the thread). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)

include hp hX hFw in
/-- **The classes of an access of `rowMax`**: warpgroup 0's, with its barrier-9 count. -/
theorem rmax_cls {c g k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access (g, k) a w) (hc : a.Covers l) (hl : MemRow.LocIn L c .rowMax l) :
    ∃ e, X.get (g, k) = some e ∧ MbarRow.warp L g < 4 ∧ Execution.isBarId 9 e = false ∧
      l.cta = g / L.block ∧ ∃ r ≤ blocksOf P L (g / L.block),
      ((X.tr g).take k).countP (Execution.isBarId 9) = (if w then 2 * r + 1 else 2 * r + 2) ∧
      (w = true → g % L.block = (l.addr - L.sharedBase - 221184) / 4) ∧
      (if w then e.pc = 566 ∨ e.pc = 1155 else e.pc = 572 ∨ e.pc = 1157) := by
  obtain ⟨e, he, hr⟩ := access_region hp hX hFw hi hc hl.1
  have hrow : MbarRow.Wg0At L g e.pc ∧ MemRow.LocIn L (g / L.block) .rowMax l := by
    rcases hr with ⟨-, h⟩ | ⟨hat, (h | h | h) | h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, r, h | h⟩ <;>
      first
      | exact ⟨hat, h⟩
      | exact absurd (locIn_eq h hl).2 (by simp)
  obtain ⟨hat, hl'⟩ := hrow
  obtain ⟨hw, hnb, r, hr, hcnt, hidx, hpc⟩ := wg0_rmaxUse hp hX hFw he hat hi hc hl'
  exact ⟨e, he, hw, hnb, hl'.2.1, r, hr, hcnt, hidx, hpc⟩

include hp hX hFw in
/-- A store and a load of a byte of `rowMax` are ordered, the one after fewer barrier-9 events
first. -/
theorem rmax_wr_rd (hR : BarRows P L X) {c g k h j : Nat} {a b : Acc} {l : Loc}
    (hi : X.Access (g, k) a true) (hj : X.Access (h, j) b false) (ha : a.Covers l)
    (hb : b.Covers l) (hl : MemRow.LocIn L c .rowMax l) :
    baseCausality L X (g, k) (h, j) ∨ baseCausality L X (h, j) (g, k) := by
  obtain ⟨e, he, hwg, hng, hcg, r, hr, hcnt, -, -⟩ := rmax_cls hp hX hFw hi ha hl
  obtain ⟨f, hf, hwh, hnh, hch, s, hs, hcnt', -, -⟩ := rmax_cls hp hX hFw hj hb hl
  have hs2 : SameCta L g h :=
    ⟨Frame.lt_of_get hX he, Frame.lt_of_get hX hf, by rw [← hcg, ← hch]⟩
  have hc1 : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 1 := by simpa using hcnt
  have hc2 : ((X.tr h).take j).countP (Execution.isBarId 9) = 2 * s + 2 := by
    simpa using hcnt'
  have hcta : h / L.block = g / L.block := hs2.2.2.symm
  by_cases hlt : 2 * r + 1 < 2 * s + 2
  · refine .inl (bar9_order hp hX hFw hR hs2 hwg he hng hj.lt (by omega) (by omega))
  · refine .inr (bar9_order hp hX hFw hR ⟨hs2.2.1, hs2.1, hcta⟩ hwh hf hnh hi.lt (by omega) ?_)
    rw [hcta] at hs ⊢
    omega

include hp hX hFw in
/-- Two stores of a byte of `rowMax` are one thread's. -/
private theorem rmax_ww {c g k h j : Nat} {a b : Acc} {l : Loc} (hi : X.Access (g, k) a true)
    (hj : X.Access (h, j) b true) (ha : a.Covers l) (hb : b.Covers l)
    (hl : MemRow.LocIn L c .rowMax l) : g = h := by
  obtain ⟨-, -, -, -, hcg, -, -, -, hg, -⟩ := rmax_cls hp hX hFw hi ha hl
  obtain ⟨-, -, -, -, hch, -, -, -, hh, -⟩ := rmax_cls hp hX hFw hj hb hl
  have h1 := hg rfl
  have h2 := hh rfl
  have hb0 : 0 < L.block := by rw [hp.block]; omega
  rw [← Nat.div_add_mod g L.block, ← Nat.div_add_mod h L.block, h1, h2, ← hcg, ← hch]

include hp hX hFw in
/-- **The row-maximum exchange is ordered**, by barrier 9. -/
theorem rowMax_ordered (hR : BarRows P L X) : RegionOrdered L X .rowMax := by
  intro e f a b l hcon ha hb hl _
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := hcon
  obtain ⟨c, hlc⟩ := hl
  obtain ⟨⟨g, k⟩, rfl⟩ := region_thread hp hX hFw (by simp) (by simp) (by simp) he ha hlc
  obtain ⟨⟨h, j⟩, rfl⟩ := region_thread hp hX hFw (by simp) (by simp) (by simp) hf hb hlc
  have he' : X.Access (g, k) a we := he
  have hf' : X.Access (h, j) b wf := hf
  have lift : ∀ {x y : EvId}, baseCausality L X x y →
      ByteCausality L X l (.thread x) (.thread y) := fun h => .direct (.of_base L h)
  cases we <;> cases wf
  · rcases hw with h | h <;> cases h
  · exact (rmax_wr_rd hp hX hFw hR hf' he' hb ha hlc).symm.imp lift lift
  · exact (rmax_wr_rd hp hX hFw hR he' hf' ha hb hlc).imp lift lift
  · obtain rfl := rmax_ww hp hX hFw he' hf' ha hb hlc
    exact same_thread he' hf' (fun h' => hne (by rw [h'])) hov l

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
