-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Sync9
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Pex
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region

@[expose] public section

/-! # The P exchange's thread accesses are ordered

A thread access of a byte of `pExchange` is warpgroup 0's (`access_region`, the rows of
`wg0_pexUse`): a peer store `pst` of block `r` after `2 r + 1` barrier-9 events and `r` of its
warp pair's, a peer load `pld` after `2 r + 1` and `r + 1`, a P store `ost` after `2 r + 2` and
`r + 1`. Two such accesses of one byte (one a write) are ordered:

* different barrier-9 counts: barrier 9 orders the one after fewer before the other
  (`bar9_order`; the counts of a `pst`/`pld` and an `ost` have different parity);
* equal counts, so both of block `r` and a `pst` and a `pld` (two `pst` or two `ost` are one
  thread's, `wg0Pst_inj`, `wg0Ost_inj`): the byte lies in the quadrant of the load's warp
  `w ^^^ 2` of the store's, the pair of one parity, and the pair barrier orders the store (count
  `r`) before the load (count `r + 1`, `barId_order`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A thread access of `pExchange`** at event `e` of lane `g`, index `k`: warpgroup 0's, not a
barrier event, in CTA `cta`, a peer store, peer load or P store of a block `r` with its counts. -/
structure PexCls (P : Params) (L : Launch) (X : Execution) (g k : Nat) (e : Event) (w : Bool)
    (o cta : Nat) : Prop where
  get : X.get (g, k) = some e
  warp : MbarRow.warp L g < 4
  n9 : Execution.isBarId 9 e = false
  np : Execution.isBarId (10 + MbarRow.warp L g % 2) e = false
  cta : cta = g / L.block
  use : ∃ r < blocksOf P L (g / L.block), PexUse (g % L.block) w o r
    (((X.tr g).take k).countP (Execution.isBarId 9))
    (((X.tr g).take k).countP (Execution.isBarId (10 + MbarRow.warp L g % 2))) ∧
    PexBlk L X g k r
  /-- A write at an even barrier-9 count is a P store (pcs 704 to 707); a peer store's is odd. -/
  ostPc : w = true → (((X.tr g).take k).countP (Execution.isBarId 9) % 2 = 0 ↔
    ∃ j < 4, e.pc = 704 + j)

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)

include hp hX hFw in
/-- **The class of a thread access of `pExchange`**: warpgroup 0's, with its place and counts. -/
theorem pex_cls {c g k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access (g, k) a w) (hc : a.Covers l) (hl : MemRow.LocIn L c .pExchange l) :
    ∃ e, PexCls P L X g k e w (l.addr - L.sharedBase - 204800) l.cta ∧
      (w = true → ∃ bs, X.Writes (g, k) a bs) := by
  obtain ⟨e, he, hr⟩ := access_region hp hX hFw hi hc hl.1
  have hrow : MbarRow.Wg0At L g e.pc ∧ MemRow.LocIn L (g / L.block) .pExchange l := by
    rcases hr with ⟨-, h⟩ | ⟨hat, (h | h | h) | h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, r, h | h⟩ <;>
      first
      | exact ⟨hat, h⟩
      | exact absurd (locIn_eq h hl).2 (by simp)
  obtain ⟨hat, hl'⟩ := hrow
  obtain ⟨hw, hn9, hnp, hcta, hwr, hu, hpar⟩ := wg0_pexUse hp hX hFw he hat hi hc hl'
  exact ⟨e, ⟨he, hw, hn9, hnp, hcta, hu, hpar⟩, hwr⟩

end

/-- A lane's warp is its thread index's. -/
theorem warp_tid (hp : Pre P L m) (g : Nat) : MbarRow.warp L g = g % L.block / 32 := by
  simp only [MbarRow.warp, tidOf_x_eq hp, hp.block]

/-- The warp of the quadrant `w ^^^ 2` has the parity of `w`. -/
theorem xor2_mod : ∀ w < 4, (w ^^^ 2) % 2 = w % 2 := by decide

/-- A thread index and a CTA index name a thread. -/
private theorem thr_eq {g h : Nat} (h1 : g % L.block = h % L.block)
    (h2 : g / L.block = h / L.block) : g = h := by
  rw [← Nat.div_add_mod g L.block, ← Nat.div_add_mod h L.block, h1, h2]

private theorem pex_n9_le {t o r n9 np : Nat} {w : Bool} (h : PexUse t w o r n9 np) :
    n9 ≤ 2 * r + 2 := by
  unfold PexUse at h
  omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : BarRows P L X)
include hp hX hFw hR

/-- A peer store is before the peer load of its warp pair's partner of the same block (equal
barrier-9 counts): the pair barrier. -/
theorem pex_sp {g k h j : Nat} {e f : Event} {o c : Nat} {w w' : Bool}
    (hg : PexCls P L X g k e w o c) (hh : PexCls P L X h j f w' o c) (hw : w = true)
    (hw' : w' = false)
    (heq : ((X.tr g).take k).countP (Execution.isBarId 9) =
      ((X.tr h).take j).countP (Execution.isBarId 9)) :
    baseCausality L X (g, k) (h, j) := by
  obtain ⟨r, hr, hu, -⟩ := hg.use
  obtain ⟨s, hs, hu', -⟩ := hh.use
  have hg' := Frame.lt_of_get hX hg.get
  have hh' := Frame.lt_of_get hX hh.get
  have hwg := warp_tid hp g
  have hwh := warp_tid hp h
  have hb := hp.block
  have hq : ∀ x : Nat, x % L.block / 32 < 4 → x % L.block / 32 ^^^ 2 < 4 := fun x hx =>
    Nat.xor_lt_two_pow (n := 2) hx (by omega)
  have hx1 := hq g (by rw [← hwg]; exact hg.warp)
  have hx2 := xor2_mod (g % L.block / 32) (by rw [← hwg]; exact hg.warp)
  subst hw hw'
  simp only [PexUse, Bool.true_eq_false, Bool.false_eq_true, false_and, or_false,
    false_or, true_and] at hu hu'
  obtain ⟨h1', h2', j2, hj2, el, hel, h3', h4'⟩ := hu'
  rcases hu with ⟨h1, h2, j1, hj1, h3, h4⟩ | ⟨h1, -⟩
  swap
  · omega
  have hh4 : h % L.block / 32 < 4 := by rw [← hwh]; exact hh.warp
  have hpar : MbarRow.warp L h % 2 = MbarRow.warp L g % 2 := by
    have e1 : h % L.block / 32 = g % L.block / 32 ^^^ 2 := by omega
    rw [hwh, hwg, e1, hx2]
  obtain rfl : r = s := by omega
  rw [hpar] at h2'
  have hmem : barIn (10 + MbarRow.warp L g % 2) ((g % L.block) / 32) = true := by
    have hg4 : g % L.block / 32 < 4 := by rw [← hwg]; exact hg.warp
    have hp2 : MbarRow.warp L g % 2 < 2 := Nat.mod_lt _ (by omega)
    simp only [barIn]
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega
  exact barId_order hp hX hR ⟨hg', hh', hg.cta.symm.trans hh.cta⟩ hmem hg.get hg.np
    (List.getElem?_eq_some_iff.mp hh.get).1 (by omega) fun jx pcx hx => by
    have := wg0_pairExit hp hX hFw hg.warp hx
    omega

/-- **Two thread accesses of one byte of `pExchange`, one a write, are ordered** (or one thread's):
by barrier 9's counts, and for a peer store and the partner's load of one block by the pair
barrier. -/
theorem pex_ord {g k h j : Nat} {e f : Event} {o c : Nat} {w w' : Bool}
    (hg : PexCls P L X g k e w o c) (hh : PexCls P L X h j f w' o c) (hw : w = true ∨ w' = true) :
    g = h ∨ baseCausality L X (g, k) (h, j) ∨ baseCausality L X (h, j) (g, k) := by
  obtain ⟨r, hr, hu, -⟩ := hg.use
  obtain ⟨s, hs, hu', -⟩ := hh.use
  have hg' := Frame.lt_of_get hX hg.get
  have hh' := Frame.lt_of_get hX hh.get
  have hcta : SameCta L g h := ⟨hg', hh', hg.cta.symm.trans hh.cta⟩
  have hcta' : SameCta L h g := ⟨hh', hg', hh.cta.symm.trans hg.cta⟩
  have b1 := pex_n9_le hu
  have b2 := pex_n9_le hu'
  rcases lt_trichotomy (((X.tr g).take k).countP (Execution.isBarId 9))
      (((X.tr h).take j).countP (Execution.isBarId 9)) with hlt | heq | hgt
  · exact .inr (.inl (bar9_order hp hX hFw hR hcta hg.warp hg.get hg.n9
      (List.getElem?_eq_some_iff.mp hh.get).1 hlt (by omega)))
  · have hwg := warp_tid hp g
    have hwh := warp_tid hp h
    have hb := hp.block
    have ht1 : g % L.block < 128 := by have := hg.warp; omega
    have ht2 : h % L.block < 128 := by have := hh.warp; omega
    unfold PexUse at hu hu'
    rcases hu with ⟨hw1, h1, h2, j1, hj1, h3, h4⟩ | ⟨hw1, h1, h2, j1, hj1, el1, hel1, h3, h4⟩ |
        ⟨hw1, h1, h2, j1, hj1, el1, hel1, h3, h4⟩ <;>
      rcases hu' with ⟨hw2, h1', h2', j2, hj2, h3', h4'⟩ |
        ⟨hw2, h1', h2', j2, hj2, el2, hel2, h3', h4'⟩ |
        ⟨hw2, h1', h2', j2, hj2, el2, hel2, h3', h4'⟩
    · refine .inl (thr_eq ?_ (hg.cta.symm.trans hh.cta))
      exact (MemRow.wg0Pst_inj ht1 ht2 hj1 hj2 (by omega)).1
    · exact .inr (.inl (pex_sp hp hX hFw hR hg hh hw1 hw2 heq))
    · omega
    · exact .inr (.inr (pex_sp hp hX hFw hR hh hg hw2 hw1 heq.symm))
    · rcases hw with h | h <;> simp_all
    · omega
    · omega
    · omega
    · refine .inl (thr_eq ?_ (hg.cta.symm.trans hh.cta))
      exact (MemRow.wg0Ost_inj ht1 ht2 hj1 hj2 hel1 hel2 (by omega)).1
  · exact .inr (.inr (bar9_order hp hX hFw hR hcta' hh.warp hh.get hh.n9
      (List.getElem?_eq_some_iff.mp hg.get).1 hgt (by omega)))

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
