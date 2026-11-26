-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Trace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlk

@[expose] public section

/-! # The carried statistics: the sites and the initial words

The sites whose arrival event has the pcs of the block cut (`1122`, `arrS`) and of the statistics'
restart (`200`, `arrL`); the data machine's `record` leaves the statistics alone off `arrL`; the
chain's step table does not go back to the set-up sites (`earlyS`) except from `arrL`; and the
words the statistics start from read as `w0M0`, `0` and `-inf`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof

noncomputable section

/-- The set-up sites, before the loop's first block. -/
def earlyS (s : Site) : Bool := decide (s ∈ [.smr, .sink, .lenA, .lenB, .bwait, .arrL])

theorem site_pc_200 {s : Site} (h : s.pc = w0ArrLPc) : s = .arrL := by
  unfold w0ArrLPc at h
  cases s
  all_goals first
    | rfl
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

theorem site_pc_1122 {s : Site} (h : s.pc = w0ArrSPc) : s = .arrS := by
  unfold w0ArrSPc at h
  cases s
  all_goals first
    | rfl
    | (exfalso; revert h; simp [Site.pc]; done)
    | (rename_i k; fin_cases k <;> (exfalso; revert h; simp [Site.pc]; done))
    | (rename_i a k; fin_cases a <;> fin_cases k <;> (exfalso; revert h; simp [Site.pc, ost2Base]))

/-- The chain's step table never goes back to a set-up site, except from `arrL`. -/
theorem succOk_back {c c' : Control.D} (h : succOk c c' = true) (hn : earlyS c'.site = false) :
    earlyS c.site = false ∨ c.site = .arrL := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hn ⊢
  by_cases hs : s = .arrL
  · exact .inr hs
  · left
    revert h hn
    cases s <;> simp [succOk, earlyS] <;> (intros; simp_all)

theorem record_stats {c : Control.D} {e : Event} {b : Blk} (h : c.site ≠ .arrL) :
    (record c e b).m = b.m ∧ (record c e b).l = b.l ∧ (record c e b).mx = b.mx := by
  unfold record
  split <;> first | exact absurd ‹_› h | exact ⟨rfl, rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl, rfl⟩)

theorem record_arrL {c : Control.D} {e : Event} {b : Blk} (h : c.site = .arrL) :
    (record c e b).m = mI ∧ (record c e b).l = lI ∧ (record c e b).mx = mxI := by
  unfold record
  split <;> first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; simp_all)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
