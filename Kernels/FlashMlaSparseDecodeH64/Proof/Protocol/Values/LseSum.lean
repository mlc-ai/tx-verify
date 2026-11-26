-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.VoteAgree
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.W0Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.BlocksOf
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos

@[expose] public section

/-! # The two lanes of a row carry its row sum

At its epilogue read (pc 1157) a lane of warpgroup 0 has finished all the CTA's blocks, and its
carried sum `l` with its carried maximum `m` is the sum of the weights of its 32 columns of each
block (`w0_lane_sum`: `ScoreRead` and `MaskRead` make the weights those of the reference's slots).
The lane and its partner (the other half of the columns) carry the same maximum (`vote_agree`), so
`(l + l') 2 ^ m` is the sum of the weights of all 64 columns of all blocks, the row sum
(`w0_pair_sum`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Valid rows give a valid trace to every lane of warpgroup 0**, launched or not. -/
theorem w0Trace_of_rows (hV : W0Rows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {y : Nat} (hw : warp L y < 4) : W0Trace P X y := by
  by_cases hy : y < L.threads
  · exact hV y hy (by simp only [warp] at hw; omega)
  · have hnil : X.tr y = [] := by
      rcases hl : X.tr y with _ | ⟨e, l⟩
      · rfl
      · exfalso
        have : X.get (y, 0) = some e := by simp [Execution.get, hl]
        exact hy (Frame.lt_of_get hX this)
    exact ⟨fun j _ => by simp [hnil, W0Now, w0Fin],
      fun j _ => Or.inl (by simp [hnil, w0Fin]),
      fun j _ => ⟨Or.inl (by simp [hnil, w0SkWord, w0NegInf]),
        Or.inl (by simp [hnil, w0Scan, w0EpiPe, w0Last]),
        Or.inl (by simp [hnil, w0Scan, w0EpiO, w0Last]),
        fun v hv => by simp [hnil, w0SkRaw] at hv⟩⟩

/-- **A lane's carried sum is its weights** (valid rows): at the lane's epilogue read, with all
the CTA's blocks finished. -/
theorem w0_lane_sum (hp : Pre P L m) (hV : W0Rows P L X) (hS : ScoreRead P L X hV)
    (hM : MaskRead P L X hV) {y k : Nat} {ev : Event} (hy : y < L.threads)
    (he : X.get (y, k) = some ev) (hpc : ev.pc = 1157)
    (hn : (w0Fin ((X.tr y).take k)).1.length = blocksOf P L (y / L.block)) :
    (w0Carry P.scale (w0Fin ((X.tr y).take k)).1).2 *
        (2 : ℝ) ^ (w0Carry P.scale (w0Fin ((X.tr y).take k)).1).1 =
      ∑ t ∈ Finset.range (Result.blocks P (w0Batch L y)), ∑ i ∈ Finset.range 32,
        Result.blockWeight P (w0Batch L y) (w0Query L y) (w0Head L y) t
          (32 * w0Half L y + i) := by
  rw [w0Carry_sum]
  have hb : (w0Fin ((X.tr y).take k)).1.length = Result.blocks P (w0Batch L y) := by
    rw [hn, blocksOf_eq hp]
    rfl
  rw [w0SumWt_eq _ _ (fun t => ∑ i ∈ Finset.range 32, Result.blockWeight P (w0Batch L y)
    (w0Query L y) (w0Head L y) t (32 * w0Half L y + i)) ?_, hb]
  intro t seg hseg
  unfold w0BlockWt
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  unfold Result.blockWeight
  rw [← w0BlockExtra_eq, ← w0BlockSlot_eq]
  exact w0Wt_eq_weight rfl (hS y k ev hy he hpc t seg hseg i hi')
    (hM y k ev hy he hpc t seg hseg i hi')

/-- **The pair's carried sums are the row sum** (valid rows, complete): the lane `g` below thread
64 and its partner, at their epilogue reads, carry the same maximum `m`, and `(l + l') 2 ^ m` is the
row sum of the lane's row. -/
theorem w0_pair_sum (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hR : BarRows P L X) (hC : Complete L X)
    (hV : W0Rows P L X) (hS : ScoreRead P L X hV) (hM : MaskRead P L X hV) {g k kq : Nat}
    {ev ev' : Event} (hw : warp L g < 4) (hg : g < L.threads) (hlow : tidOf L g < 64)
    (he : X.get (g, k) = some ev) (hpc : ev.pc = 1157)
    (he' : X.get (w0Partner L g, kq) = some ev') (hpc' : ev'.pc = 1157)
    (hn : (w0Fin ((X.tr g).take k)).1.length = blocksOf P L (g / L.block))
    (hn' : (w0Fin ((X.tr (w0Partner L g)).take kq)).1.length = blocksOf P L (g / L.block)) :
    (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 =
        (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1).1 ∧
      ((w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2 +
          (w0Carry P.scale (w0Fin ((X.tr (w0Partner L g)).take kq)).1).2) *
        (2 : ℝ) ^ (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 =
      rowSum P (w0Batch L g) (w0Query L g) (w0Head L g) := by
  obtain ⟨⟨hpt, -, -⟩, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  have hV' : ∀ y, warp L y < 4 → W0Trace P X y := fun y hy => w0Trace_of_rows hV hX hy
  have hag := vote_agree hp hX hFw hnu hR hC hV' hw hg hn hn'
  have h1 := w0_lane_sum hp hV hS hM hg he hpc hn
  have h2 := w0_lane_sum hp hV hS hM hpt he' hpc' (by rw [hdiv]; exact hn')
  have hx := tidOf_x_eq hp g
  have hxp := tidOf_x_eq hp (w0Partner L g)
  have hb : L.block = 384 := by have := hp.block; omega
  have hlow' : g % 384 < 64 := by simp only [tidOf, hx] at hlow; exact hlow
  have hxor : (g % 384) ^^^ 64 = g % 384 + 64 := by
    have := xor64_of_lt (g % 384) (by omega)
    simpa [hlow'] using this
  have hxp' : (L.tidOf (w0Partner L g)).x = g % 384 + 64 := by
    rw [hxp, ← hb, hmod, hb, hxor]
  have hbat : w0Batch L (w0Partner L g) = w0Batch L g := by unfold w0Batch; rw [hdiv]
  have hqu : w0Query L (w0Partner L g) = w0Query L g := by unfold w0Query; rw [hdiv]
  have hhd : w0Head L (w0Partner L g) = w0Head L g := by
    unfold w0Head; rw [hxp', hx]; omega
  have hh0 : w0Half L g = 0 := by unfold w0Half; rw [hx]; omega
  have hh1 : w0Half L (w0Partner L g) = 1 := by unfold w0Half; rw [hxp']; omega
  rw [hbat, hqu, hhd, hh1] at h2
  rw [hh0] at h1
  refine ⟨hag, ?_⟩
  rw [add_mul, h1, hag, h2, ← Finset.sum_add_distrib]
  obtain ⟨-, -, -, htopk, hextra⟩ := len_words hp (g / L.block)
  have hrow : rowOf L (g / L.block) = w0Batch L g := rfl
  rw [hrow] at htopk hextra
  rw [← Result.sum_blockWeight_eq_rowSum P _ (w0Query L g) (w0Head L g) htopk hextra]
  refine Finset.sum_congr rfl fun t _ => ?_
  have := Finset.sum_range_add (fun j => Result.blockWeight P (w0Batch L g) (w0Query L g)
    (w0Head L g) t j) 32 32
  simp only [Result.topkBlock] at this ⊢
  rw [show (64 : Nat) = 32 + 32 from rfl, this]
  simp

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
