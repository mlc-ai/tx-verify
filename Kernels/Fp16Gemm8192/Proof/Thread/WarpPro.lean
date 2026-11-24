-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.WarpStage

@[expose] public section

/-! # The prologue's collective sites: positions and lanes

A thread's prologue state before its `k`-th event is at index `k` (`stateAt_prologue`). Warp 0
reaches its election at index 1 and its warp barrier at index `wbIdx` (3, or 22 for the CTA's
thread 0), the shuffle is every thread's event 0. So a thread at one of these sites has made none
of the site's events, and a lane of its warp has either made the site's event (it is past the
site's index), or is at the site, or at an earlier site of time at least 2 less, or stopped before
the site without exiting. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The index of warp 0's warp barrier. -/
def wbIdx (L : Launch) (g : Nat) : Nat := index L g ⟨.warpBar, 0⟩

/-- Warp 0's prologue states up to the warp barrier: the warp barrier at its index, and the earlier
sites, of time at most 42. -/
theorem w0_site {p : D} (hw : p.site ≠ .shfl → p.w = 0) (hc : Canon L g p)
    (hle : index L g p ≤ wbIdx L g) :
    (index L g p = wbIdx L g → p.site = .warpBar) ∧
      (index L g p < wbIdx L g → p.site.vtime + 2 ≤ 44) := by
  obtain ⟨site, w⟩ := p
  obtain ⟨-, hinit, hwrite, hset, hrole⟩ := hc
  simp only at hw hinit hwrite hset hrole
  cases site with
  | shfl => simp [Prologue.index, wbIdx, Site.vtime]; cases first L g <;> simp
  | elect => simp [Prologue.index, wbIdx, Site.vtime]; cases first L g <;> simp
  | init i =>
    have hf := hinit i rfl
    have := i.isLt
    simp [Prologue.index, wbIdx, Site.vtime, hf]
    omega
  | alloc => simp [Prologue.index, wbIdx, Site.vtime]; cases first L g <;> simp
  | allocWrite =>
    have hf := hwrite rfl
    simp [Prologue.index, wbIdx, Site.vtime, hf]
  | warpBar => simp [Prologue.index, wbIdx]
  | fence | fenceInit | arrive | wait =>
    have hw0 := hw (by simp)
    subst hw0
    simp [Prologue.index, wbIdx, Prologue.fenceIdx] at hle ⊢
    split_ifs at hle <;> omega
  | setMaxReg => have := hset rfl; have := hw (by simp); omega
  | roleElect => have := hrole rfl; have := hw (by simp); omega

/-- Warp 0's warp barrier comes before its cluster wait. -/
theorem wbIdx_lt_wait : wbIdx L g < index L g ⟨.wait, 0⟩ := by
  simp only [wbIdx, Prologue.index, Prologue.fenceIdx, ↓reduceIte]
  split_ifs <;> omega

/-- A prologue state at the end of a run is at the index of the run's length. -/
theorem pro_end (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {k : Nat} (hk : k ≤ (X.tr g).length) {p : D} (hσ : Frame.stateAt (code L) X g k =
      some (some (.inl p))) :
    k = index L g p ∧ (0 < k → p.w = warpOf L g) ∧ Canon L g p :=
  (onPath_all hpre hX hg k hk).1 p hσ

/-- An exit is fired after the prologue's cluster wait. -/
theorem exit_after_wait (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    index L g ⟨.wait, warpOf L g⟩ < k := by
  obtain ⟨d, hσ, hx⟩ := exit_event_state' hpre hX hg he
  rcases d with p | r
  · exact absurd rfl hx
  · exact (onPath_all hpre hX hg k (len_of_get he).le).2 r hσ

/-- A stopped thread before its cluster wait has not exited. -/
theorem not_exit_before_wait (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) (hle : (X.tr g).length ≤ index L g ⟨.wait, warpOf L g⟩ + 1) :
    ∀ pc, (X.tr g).getLast? ≠ some ⟨pc, .exit⟩ := by
  intro pc hl
  have hpos : 0 < (X.tr g).length := by
    rcases h : X.tr g with _ | ⟨x, xs⟩
    · rw [h] at hl; cases hl
    · simp
  have he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hl
  have := exit_after_wait hpre hX hg he
  omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
