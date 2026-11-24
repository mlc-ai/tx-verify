-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOut

@[expose] public section

/-! # The correction warps' parts of the cross-warp premises

From the correction thread's reads (its statistics words, below `+1356`), its writes (its rows'
staging lines, from `+3072` to below `+68608`), its arrivals (the statistics credits, the staged
barriers, the leader's P-ready barriers) and its polls (the O-full and free barriers of its CTA):

* every access of a correction thread lies below `+68608` (`Cross.lowAccessLow_corr`) and none
  covers the base word `+328 … +331` (`Cross.baseFree_corr`);
* every arrival and poll of a correction thread names a table barrier that is not spare, of a
  CTA of the thread's pair (`Cross.syncNamed_corr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- The footprint of a correction thread's access: a statistics word or a staging line. -/
theorem corr_access_range {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (h : X.Access (g, k) a w) (hc : a.Covers l) :
    (L.sharedBase + 332 ≤ l.addr ∧ l.addr < L.sharedBase + 1356) ∨
      (L.sharedBase + 3072 ≤ l.addr ∧ l.addr < L.sharedBase + 68608) := by
  have hr : rowOf L g < 128 := rowOf_lt L g
  obtain ⟨-, -, h1, h2⟩ := hc
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨_, _, pc, he⟩
  rotate_right
  · exact (TmemFacts_no_rmw hX he).elim
  · obtain ⟨-, st, -, -, -, -, -, hl, hs, -⟩ := corr_rd hpre hX ht hw hw' he
    rw [hl] at h1 h2
    rw [hs] at h2
    simp only [statsWord] at h1 h2
    have := st.isLt
    left; constructor <;> omega
  · obtain ⟨-, st, j, hh, el, -, -, -, -, hl, hs, -⟩ := corr_wr hpre hX ht hw hw' he
    obtain ⟨-, -, h3, h4⟩ := fst_inLine st j hh el hl hs
    simp only [lineBase] at h3 h4
    have := st.isLt
    have := j.isLt
    right; constructor <;> omega

/-- **`LowAccessLow`, correction part.** -/
theorem lowAccessLow_corr {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (h : X.Access (g, k) a w) (hc : a.Covers l) :
    l.addr < L.sharedBase + 68608 := by
  rcases corr_access_range hpre hX ht hw hw' h hc with h' | h' <;> omega

/-- **`BaseFree`, correction part.** -/
theorem baseFree_corr {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (h : X.Access (g, k) a w) (hc : a.Covers l)
    (h1 : L.sharedBase + 328 ≤ l.addr) (h2 : l.addr < L.sharedBase + 332) : False := by
  rcases corr_access_range hpre hX ht hw hw' h hc with h' | h' <;> omega

/-- **`SyncNamed`, correction part.** -/
theorem syncNamed_corr {g k pc : Nat} {m : Loc} {kd : Kind} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, k) = some ⟨pc, kd⟩)
    (hk : (∃ tx c rel sc, kd = .arrive m tx c rel sc) ∨ (∃ p ok acq sc, kd = .wait m p ok acq sc)) :
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L g / 2 ∧ ∀ i st, b ≠ .spare i st := by
  rcases hk with ⟨tx, c, rel, sc, rfl⟩ | ⟨p, ok, acq, sc, rfl⟩
  · obtain ⟨-, -, d, -, -, -, -, hs⟩ := corr_arrive hpre hX ht hw hw' he
    rcases hs with ⟨a, -, rfl⟩ | ⟨st, -, rfl⟩ | ⟨st, -, rfl⟩
    · exact ⟨.stats ⟨a.val % 2, Nat.mod_lt _ (by decide)⟩, ctaOf L g, rfl, rfl, by simp⟩
    · exact ⟨.oStaged st, ctaOf L g, rfl, rfl, by simp⟩
    · exact ⟨.pReady st, 2 * (ctaOf L g / 2), rfl, by omega, by simp⟩
  · obtain ⟨d, -, -, -, -, hs⟩ := corr_wait hpre hX ht hw hw' he
    rcases hs with ⟨st, -, rfl, -⟩ | ⟨st, -, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact ⟨.oFull st, ctaOf L g, rfl, rfl, by simp⟩
    · exact ⟨.oFree st, ctaOf L g, rfl, rfl, by simp⟩
    · exact ⟨.oFree 1, ctaOf L g, rfl, rfl, by simp⟩

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
