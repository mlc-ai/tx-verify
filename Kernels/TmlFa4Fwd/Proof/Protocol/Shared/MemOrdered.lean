-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
public import Lemmas.Protocol.RegionByte
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.CopySource
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.GlobalOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Ordered

@[expose] public section

/-! # The conflicts of memory are ordered, but for the output writes of one byte

Conflicts in shared and in local memory are ordered; the global writes are LSE words and O bytes,
which no access reads (`read_input`). So the conflicts at the bytes that are read are ordered
(`reads_ordered`), no two conflicting accesses of different footprints are unordered (`no_mixed`),
and the races left are of two output writes of one footprint (`no_race`, from `OutOrdered`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The output writes of one byte are ordered, or write the same value.** -/
def OutOrdered (p : Params) (L : Launch) (X : Execution) : Prop :=
  ByteOrdered L X fun l => p.oRegion.Contains l ∨ p.lseRegion.Contains l

theorem not_both {r r' : Region} {l : Loc} (h : r.Apart r') (h1 : r.Contains l)
    (h2 : r'.Contains l) : False := by
  obtain ⟨-, -, a1, a2⟩ := h1
  obtain ⟨-, -, b1, b2⟩ := h2
  rcases h with h | h <;> omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A global byte that is read is an input byte.** -/
theorem read_input {r : Ref} {a : Acc} {l : Loc} (hi : X.Intent r a false) (hc : a.Covers l)
    (hl : l.space = .global) : ∃ rg ∈ p.inputRegions, rg.Contains l := by
  have hs : a.loc.space = .global := hc.1.symm.trans hl
  have hns : a.loc.space ≠ .shared := by rw [hs]; decide
  obtain ⟨-, h2, h3, h4⟩ := id hc
  rcases outside_read hp hX hFw hi hns with ⟨hz, h⟩ | ⟨g, k, -, o, hloc, -⟩ | ⟨i, sp, hcp, rfl⟩ |
    ⟨hz, h⟩
  · rw [hz] at h4
    rcases h with ⟨i, hi', hloc⟩ | ⟨i, hi', hloc⟩ | ⟨i, hi', q, hq, hloc⟩ <;>
      rw [hloc] at h2 h3 h4 <;> simp only [globalLoc] at h2 h3 h4
    · exact ⟨⟨p.cuQBase, 4 * (p.batch + 1)⟩, by simp [Params.inputRegions], hl, h2,
        by simp only; omega, by simp only; omega⟩
    · exact ⟨⟨p.usedKBase, 4 * p.batch⟩, by simp [Params.inputRegions], hl, h2,
        by simp only; omega, by simp only; omega⟩
    · refine ⟨⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩, by simp [Params.inputRegions],
        hl, h2, by simp only; omega, ?_⟩
      obtain ⟨hst, -⟩ := hp.pageTable i hi'
      have hmul : p.pageTableStride * (i + 1) ≤ p.pageTableStride * p.batch :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ, Nat.mul_comm p.pageTableStride i] at hmul
      have hassoc : 4 * p.batch * p.pageTableStride = 4 * (p.pageTableStride * p.batch) := by
        rw [Nat.mul_assoc, Nat.mul_comm p.batch]
      simp only
      omega
  · rw [hloc] at hs; cases hs
  · obtain ⟨page, hpg, h, hh, r, hr, d, hd, y, hy, hlk⟩ := cpSrc hp hX hFw i sp l hcp hc
    have hreg : ∀ c : CacheLayout, l = (c.loc page h r d).at y →
        (c.region p.pages p.kvHeads).Contains l := by
      rintro c rfl
      have e1 := Nat.mul_le_mul_right c.pageStride (show page ≤ p.pages - 1 by omega)
      have e2 := Nat.mul_le_mul_right c.headStride (show h ≤ p.kvHeads - 1 by omega)
      have e3 := Nat.mul_le_mul_right c.rowStride (show r ≤ 15 by omega)
      refine ⟨rfl, rfl, ?_, ?_⟩ <;>
        simp only [CacheLayout.region, CacheLayout.loc, globalLoc, Loc.at] <;> omega
    rcases hlk with hlk | hlk
    · exact ⟨_, by simp [Params.inputRegions], hreg p.kLayout hlk⟩
    · exact ⟨_, by simp [Params.inputRegions], hreg p.vLayout hlk⟩
  · obtain rfl := loc_of_one hz hc
    have box : ∀ {cols rows q h d y base : Nat}, q < rows → h < p.heads → d < cols → y < 2 →
        Region.Contains ⟨base, 2 * cols * p.heads * rows⟩
          ((globalLoc (base + 2 * ((q * p.heads + h) * cols + d))).at y) := by
      intro cols rows q h d y base hq hh hd hy
      have hrow := Nat.mul_le_mul_right p.heads (show q + 1 ≤ rows by omega)
      rw [Nat.add_mul, Nat.one_mul] at hrow
      have hcol := Nat.mul_le_mul_right cols (show q * p.heads + h + 1 ≤ rows * p.heads by omega)
      rw [Nat.add_mul, Nat.one_mul] at hcol
      have e : 2 * cols * p.heads * rows = 2 * (rows * p.heads * cols) := by ring
      rw [e]
      exact ⟨rfl, rfl, by simp only [globalLoc, Loc.at]; omega,
        by simp only [globalLoc, Loc.at]; omega⟩
    rcases h with ⟨q, hq, h, hh, d, hd, y, hy, hloc⟩ | ⟨q, hq, h, hh, d, hd, y, hy, hloc⟩ <;>
      rw [hloc]
    · exact ⟨⟨p.qBase, 2 * 128 * p.heads * p.totalQ⟩, by simp [Params.inputRegions],
        box hq hh hd hy⟩
    · exact ⟨⟨p.biasBase, 2 * 1280 * p.heads * (p.totalQ + 128)⟩, by simp [Params.inputRegions],
        box hq hh hd hy⟩

/-- **A conflict outside shared and local memory is of two output writes.** -/
theorem out_conflict {e f : Ref} {a b : Acc} {l : Loc} (hcon : Conflict X e f a b)
    (ha : a.Covers l) (hb : b.Covers l) (hs : l.space ≠ .shared) (hlo : l.space ≠ .local) :
    X.Intent e a true ∧ X.Intent f b true ∧ l.space = .global ∧
      (p.oRegion.Contains l ∨ p.lseRegion.Contains l) := by
  obtain ⟨-, we, wf, he, hf, hw, -⟩ := hcon
  have key : ∀ {r : Ref} {c : Acc}, X.Intent r c true → c.Covers l →
      l.space = .global ∧ (p.oRegion.Contains l ∨ p.lseRegion.Contains l) := by
    intro r c hi hc
    have hsp : l.space = .global := by
      rcases outside_write hp hX hFw hi (by rw [← hc.1]; exact hs) with h | ⟨g, k, -, o, hloc, -⟩
      · exact hc.1.trans h
      · exact (hlo (by rw [hc.1, hloc])).elim
    exact ⟨hsp, global_write_region hp hX hFw hi hc hsp⟩
  have noread : ∀ {r : Ref} {c : Acc}, X.Intent r c false → c.Covers l → l.space = .global →
      (p.oRegion.Contains l ∨ p.lseRegion.Contains l) → False := by
    intro r c hi hc hg ho
    obtain ⟨rg, hrg, hin⟩ := read_input hp hX hFw hi hc hg
    obtain ⟨h1, h2⟩ := hp.separate.2 rg hrg
    rcases ho with ho | ho
    · exact not_both h1 ho hin
    · exact not_both h2 ho hin
  rcases hw with rfl | rfl
  · obtain ⟨h1, h2⟩ := key he ha
    cases wf with
    | true => exact ⟨he, hf, h1, h2⟩
    | false => exact (noread hf hb h1 h2).elim
  · obtain ⟨h1, h2⟩ := key hf hb
    cases we with
    | true => exact ⟨he, hf, h1, h2⟩
    | false => exact (noread he ha h1 h2).elim

/-- **Memory is ordered**, given the output writes. -/
theorem mem_ordered (hO : OutOrdered p L X) : ByteOrdered L X fun _ => True := by
  intro e f a b l hcon ha hb _ hE
  by_cases hs : l.space = .shared
  · exact shared_ordered hp hX hFw e f a b l hcon ha hb hs hE
  by_cases hlo : l.space = .local
  · exact (local_ordered hp hX hFw (cpSrc hp hX hFw)).byte e f a b l hcon ha hb hlo hE
  · obtain ⟨-, -, -, ho⟩ := out_conflict hp hX hFw hcon ha hb hs hlo
    exact hO e f a b l hcon ha hb ho hE

/-- **No race**, given the order of the output writes. -/
theorem no_race (hO : OutOrdered p L X) : ¬ Race L X := (mem_ordered hp hX hFw hO).no_race

/-- **The conflicts at the bytes that are read are ordered.** -/
theorem reads_ordered : ReadsOrdered L X := by
  intro r ra rbs k hr hk e f a b hcon hE ha hb
  have hc : ra.Covers (ra.loc.at k) := Acc.covers_at hk
  by_cases hs : (ra.loc.at k).space = .shared
  · exact shared_ordered hp hX hFw e f a b _ hcon ha hb hs hE
  by_cases hlo : (ra.loc.at k).space = .local
  · exact (local_ordered hp hX hFw (cpSrc hp hX hFw)).byte e f a b _ hcon ha hb hlo hE
  · exfalso
    obtain ⟨-, -, hg, ho⟩ := out_conflict hp hX hFw hcon ha hb hs hlo
    obtain ⟨rg, hrg, hin⟩ := read_input hp hX hFw hr.intent hc hg
    obtain ⟨h1, h2⟩ := hp.separate.2 rg hrg
    rcases ho with ho | ho
    · exact not_both h1 ho hin
    · exact not_both h2 ho hin

/-- **No mixed-size conflict.** -/
theorem no_mixed : ¬ Mixed L X := by
  rintro ⟨e, f, a, b, l, hcon, hsf, ha, hb, h1, h2⟩
  by_cases hE : SameValueWrites X e f a b
  · exact hsf hE.2.2.1
  by_cases hs : l.space = .shared
  · exact (shared_ordered hp hX hFw e f a b l hcon ha hb hs hE).elim h1 h2
  by_cases hlo : l.space = .local
  · exact ((local_ordered hp hX hFw (cpSrc hp hX hFw)).byte e f a b l hcon ha hb hlo hE).elim h1 h2
  obtain ⟨he, hf, hg, -⟩ := out_conflict hp hX hFw hcon ha hb hs hlo
  refine hsf ?_
  have hga : a.loc.space = .global := ha.1.symm.trans hg
  have hgb : b.loc.space = .global := hb.1.symm.trans hg
  have hlse : ∀ {c : Acc} {q h : Nat}, q < p.totalQ → h < p.heads → c.loc = p.lseLoc q h →
      c.size = 4 → c.Covers l → p.lseRegion.Contains l := by
    intro c q h hq hh hloc hz hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    rw [hloc] at c2 c3 c4
    rw [hz] at c4
    have hmul := Nat.mul_le_mul_right p.lseStride (show h ≤ p.heads - 1 by omega)
    simp only [Params.lseLoc, globalLoc] at c2 c3 c4
    exact ⟨hg, c2, by simp only [Params.lseRegion]; omega, by simp only [Params.lseRegion]; omega⟩
  rcases global_write_shape hp hX hFw he hga with ⟨q, hq, h, hh, hloc, hz⟩ | ⟨hz, ho⟩ <;>
    rcases global_write_shape hp hX hFw hf hgb with ⟨q', hq', h', hh', hloc', hz'⟩ | ⟨hz', ho'⟩
  · have hll : a.loc = b.loc := by
      obtain ⟨c1, c2, c3, c4⟩ := ha
      obtain ⟨d1, d2, d3, d4⟩ := hb
      rw [hloc] at c3 c4
      rw [hloc'] at d3 d4
      rw [hz] at c4
      rw [hz'] at d4
      rw [hloc, hloc']
      simp only [Params.lseLoc, globalLoc] at c3 c4 d3 d4 ⊢
      simp only [Loc.mk.injEq, true_and]
      generalize h * p.lseStride + q = A at *
      generalize h' * p.lseStride + q' = B at *
      omega
    exact ⟨hll, hz.trans hz'.symm⟩
  · exfalso
    obtain rfl := loc_of_one hz' hb
    exact not_both hp.separate.1 ho' (hlse hq hh hloc hz ha)
  · exfalso
    obtain rfl := loc_of_one hz ha
    exact not_both hp.separate.1 ho (hlse hq' hh' hloc' hz' hb)
  · exact ⟨(loc_of_one hz ha).trans (loc_of_one hz' hb).symm, hz.trans hz'.symm⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
