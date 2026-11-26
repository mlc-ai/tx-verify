-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Result.Softmax
public import Lemmas.Real.BlockSums
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The blockwise online softmax of one sparse-decode row

This module connects the kernel's per-block update of the softmax accumulators to `attn`
and `lse`, for one `(batch, query, head)` row. Everything is pure real algebra over
`Params`.

The kernel visits `blocks P e` blocks of `B_TOPK = 64` slots (`kernel.cuh:124,132`): the first
`origBlocks P e` blocks read the main cache, the rest the extra cache, and an extra block's slot
positions are rebased on the main block count (`kernel.cuh:563`). `Run` records the kernel's
first-block write and its per-block rescale-and-add of the O accumulator and the row sum
(`kernel.cuh:195-270`). The reference exponents `c` are the kernel's `mi`; they are arbitrary
reals here (the kernel's are nondecreasing, but nothing below uses that).

The results are:

* `Run.acc`, `Run.sum`: after block `τ` the accumulators hold the weights of the blocks `≤ τ`
  against `c τ` (`PTX.Numeric.sparse_acc`, `PTX.Numeric.sparse_sum`).
* `sum_blockWeight_eq_rowSum`, `sum_blockWeight_mul_value_eq_numerator`: the double sums over
  blocks and slots flatten to `rowSum` and `numerator`, covering both caches and their
  padded slots.
* `Run.final_sink`, `Run.final_noSink`: the final accumulator over the row sum and the sink term
  is `attn`. The sink term is `2 ^ (sinkLog2 P h - c) = sinkWeight P h · 2 ^ (-c)`; without
  a sink the kernel's `attn_sink` is `-inf` and the term is `0`, which no real `2 ^ x` equals, so
  that case is stated separately.
* `Run.final_log`: `c (n - 1) · ln 2 + ln (l (n - 1))` is the natural log of the row sum.
* `Run.final_lse`: the epilogue scales the base-2 log by its compiled binary32 factor.
* `Run.final_empty`: a zero row sum gives a zero accumulator and `attn = 0`.

## The block arithmetic mirror

`Data/Indices.lean` and `Spec.lean` cannot be imported together: both declare
`PTX.Kernels.FlashMlaSparseDecodeH64.slotValid` (the spec's `slotValid P e q extra j` and the
kernel model's `slotValid len extraLen b lane i idx`), and Lean has no way to import one of the
two. The section "Block arithmetic" below therefore restates the block-budget functions and
lemmas of `Data/Indices.lean` verbatim (with its docstrings) in this namespace. Once one of the
two `slotValid`s is renamed, this section should be deleted and its uses replaced by the
`Indices.*` names. The rest of the file uses only `Spec` and these mirrors.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Finset
open PTX.Numeric

noncomputable section

/-! ## Block arithmetic (mirror of `Data/Indices.lean`) -/

/-- `B_TOPK` (`config.h:48`): the number of sparse indices one block covers.
(Mirror of `Data/Indices.topkBlock`.) -/
def topkBlock : Nat := 64

/-- `ku::ceil(a, b) = (a + b - 1) / b * b` (`kerutils/common/common.h:36-39`). Mirror of
`Data/Indices.ceilToMultiple`. -/
def ceilToMultiple (n d : Nat) : Nat := (n + d - 1) / d * d

/-- `orig_topk_padded = max(ku::ceil(topk_length, B_TOPK), B_TOPK)` (`kernel.cuh:122`). Mirror of
`Data/Indices.origPadded`. -/
def origPadded (len : Nat) : Nat := max (ceilToMultiple len topkBlock) topkBlock

/-- `orig_topk_padded / B_TOPK` (`kernel.cuh:142`). Mirror of
`Data/Indices.numOrigBlocks`. -/
def numOrigBlocks (len : Nat) : Nat := origPadded len / topkBlock

/-- `total_topk_padded / B_TOPK` (`kernel.cuh:124,132`). Mirror of
`Data/Indices.totalBlocks`. -/
def totalBlocks (len extraLen : Nat) : Nat :=
  (origPadded len + ceilToMultiple extraLen topkBlock) / topkBlock

/-- `block_idx >= num_orig_kv_blocks` (`kv_cache_utils.cuh:12-27`, `kernel.cuh:555,563`).
Mirror of `Data/Indices.isExtraBlock`. -/
def isExtraBlock (b len : Nat) : Bool := decide (numOrigBlocks len ≤ b)

theorem le_ceilToMultiple {n d : Nat} (hd : 0 < d) : n ≤ ceilToMultiple n d := by
  have h := Nat.div_add_mod' (n + d - 1) d
  have hr := Nat.mod_lt (n + d - 1) hd
  unfold ceilToMultiple
  omega

theorem ceilToMultiple_mod (n d : Nat) : ceilToMultiple n d % d = 0 := by
  unfold ceilToMultiple
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left d _)

theorem origPadded_mod (len : Nat) : origPadded len % topkBlock = 0 := by
  unfold origPadded
  rcases Nat.le_total (ceilToMultiple len topkBlock) topkBlock with h | h
  · rw [Nat.max_eq_right h, Nat.mod_self]
  · rw [Nat.max_eq_left h, ceilToMultiple_mod]

theorem numOrigBlocks_mul (len : Nat) : numOrigBlocks len * topkBlock = origPadded len := by
  unfold numOrigBlocks
  exact Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr (origPadded_mod len))

theorem origPadded_pos (len : Nat) : 0 < origPadded len := by
  unfold origPadded
  exact lt_of_lt_of_le (by decide : (0 : Nat) < topkBlock) (Nat.le_max_right _ _)

theorem numOrigBlocks_pos (len : Nat) : 0 < numOrigBlocks len := by
  have h := numOrigBlocks_mul len
  rcases Nat.eq_zero_or_pos (numOrigBlocks len) with h0 | hpos
  · rw [h0, Nat.zero_mul] at h
    have := origPadded_pos len
    omega
  · exact hpos

theorem totalBlocks_eq (len extraLen : Nat) :
    totalBlocks len extraLen =
      numOrigBlocks len + ceilToMultiple extraLen topkBlock / topkBlock := by
  unfold totalBlocks
  rw [← numOrigBlocks_mul len]
  rw [Nat.add_comm (numOrigBlocks len * topkBlock) (ceilToMultiple extraLen topkBlock)]
  rw [Nat.add_mul_div_right _ _ (by decide : 0 < topkBlock)]
  exact Nat.add_comm _ _

theorem numOrigBlocks_le_totalBlocks (len extraLen : Nat) :
    numOrigBlocks len ≤ totalBlocks len extraLen := by
  rw [totalBlocks_eq]
  exact Nat.le_add_right _ _

theorem totalBlocks_pos (len extraLen : Nat) : 0 < totalBlocks len extraLen :=
  lt_of_lt_of_le (numOrigBlocks_pos len) (numOrigBlocks_le_totalBlocks len extraLen)

theorem isExtraBlock_eq_true_iff {len b : Nat} :
    isExtraBlock b len = true ↔ numOrigBlocks len ≤ b :=
  decide_eq_true_iff

/-! ## The row's block enumeration -/

/-- `total_topk_padded / B_TOPK` (`kernel.cuh:124,132`): the number of KV blocks one
`(batch e, query q)` row visits. The kernel's block loops run `for (block_idx = start_block_idx;
block_idx < end_block_idx; ++block_idx)` with `start_block_idx = 0` and `end_block_idx =
total_topk_padded / B_TOPK` in the no-split instance (`kernel.cuh:131-133,195,600,610`), main
cache's blocks first and extra cache's after them. The count uses the row's *runtime* lengths
`P.topkLen e` / `P.extraTopkLen e`, not the declared budgets `P.topk` / `P.extra_topk`. -/
def blocks (P : Params) (e : Nat) : Nat :=
  totalBlocks (P.topkLen e) (P.extraTopkLen e)

/-- The row's main-cache block count, `orig_topk_padded / B_TOPK` (`kernel.cuh:142`). -/
def origBlocks (P : Params) (e : Nat) : Nat :=
  numOrigBlocks (P.topkLen e)

/-- The kernel's block count as the C computes it, `total_topk_padded / B_TOPK`. -/
theorem blocks_eq_kernel (P : Params) (e : Nat) :
    blocks P e = (origPadded (P.topkLen e) +
      ceilToMultiple (P.extraTopkLen e) topkBlock) / topkBlock := rfl

/-- The main-cache and extra-cache block counts add up (`kernel.cuh:124,142`). -/
theorem blocks_eq (P : Params) (e : Nat) :
    blocks P e = origBlocks P e +
      ceilToMultiple (P.extraTopkLen e) topkBlock / topkBlock :=
  totalBlocks_eq (P.topkLen e) (P.extraTopkLen e)

/-- Every row visits at least one main-cache block: `orig_topk_padded ≥ B_TOPK`
(`kernel.cuh:122`). -/
theorem blocks_pos (P : Params) (e : Nat) : 0 < blocks P e :=
  totalBlocks_pos (P.topkLen e) (P.extraTopkLen e)

theorem origBlocks_le_blocks (P : Params) (e : Nat) : origBlocks P e ≤ blocks P e :=
  numOrigBlocks_le_totalBlocks (P.topkLen e) (P.extraTopkLen e)

/-- Whether block `τ` reads the extra cache (`IS_EXTRA_BLOCK`, `kernel.cuh:555,563`). -/
def blockExtra (P : Params) (e τ : Nat) : Bool :=
  isExtraBlock τ (P.topkLen e)

/-- Position of slot `j` of block `τ` in its own cache's index array: `block_idx*B_TOPK + j`,
rebased on the main-cache block count for an extra block (`kernel.cuh:563`). -/
def blockSlot (P : Params) (e τ j : Nat) : Nat :=
  if blockExtra P e τ then (τ - origBlocks P e) * topkBlock + j
  else τ * topkBlock + j

theorem blockExtra_false {P : Params} {e τ : Nat} (h : τ < origBlocks P e) :
    blockExtra P e τ = false := by
  have h' : τ < numOrigBlocks (P.topkLen e) := h
  unfold blockExtra isExtraBlock
  exact decide_eq_false_iff_not.mpr (not_le.mpr h')

theorem blockExtra_true {P : Params} {e τ : Nat} (h : origBlocks P e ≤ τ) :
    blockExtra P e τ = true := by
  have h' : numOrigBlocks (P.topkLen e) ≤ τ := h
  unfold blockExtra isExtraBlock
  exact decide_eq_true_iff.mpr h'

theorem blockSlot_false {P : Params} {e τ j : Nat} (h : blockExtra P e τ = false) :
    blockSlot P e τ j = τ * topkBlock + j := by
  simp [blockSlot, h]

theorem blockSlot_true {P : Params} {e τ j : Nat} (h : blockExtra P e τ = true) :
    blockSlot P e τ j = (τ - origBlocks P e) * topkBlock + j := by
  simp [blockSlot, h]

/-! ## The weight and value of a block slot -/

/-- The unnormalized weight of slot `j` of block `τ`: `weight` at the block's cache tag and
position. An invalid slot has weight `0`. -/
def blockWeight (P : Params) (e q h : Nat) (τ j : Nat) : ℝ :=
  weight P e q h (blockExtra P e τ) (blockSlot P e τ j)

/-- The value of channel `d` of slot `j` of block `τ`. -/
def blockValue (P : Params) (e q : Nat) (τ j d : Nat) : ℝ :=
  slotValue P e q (blockExtra P e τ) (blockSlot P e τ j) d

/-- A slot `slotValid` accepts lies below its cache's runtime length. -/
theorem slotValid_lt_len {P : Params} {e q : Nat} {extra : Bool} {σ : Nat}
    (h : slotValid P e q extra σ) :
    σ < (if extra then P.extraTopkLen e else P.topkLen e) := by
  unfold slotValid at h
  exact h.1

/-- A main-cache weight past the runtime length is zero. -/
theorem weight_false_eq_zero_of_ge {P : Params} {e q h σ : Nat} (hσ : P.topkLen e ≤ σ) :
    weight P e q h false σ = 0 := by
  have hns : ¬ slotValid P e q false σ := by
    intro hs
    have hlt := slotValid_lt_len hs
    simp only [Bool.false_eq_true, ite_false] at hlt
    omega
  simp only [weight, ite_eq_right hns]

/-- An extra-cache weight past the runtime length is zero. -/
theorem weight_true_eq_zero_of_ge {P : Params} {e q h σ : Nat} (hσ : P.extraTopkLen e ≤ σ) :
    weight P e q h true σ = 0 := by
  have hns : ¬ slotValid P e q true σ := by
    intro hs
    have hlt := slotValid_lt_len hs
    simp only [ite_true] at hlt
    omega
  simp only [weight, ite_eq_right hns]

/-- A weight is nonnegative: a valid slot's weight is a positive power of two. -/
theorem weight_nonneg (P : Params) (e q h : Nat) (extra : Bool) (j : Nat) :
    0 ≤ weight P e q h extra j := by
  unfold weight
  split
  · exact (two_rpow_pos (P.scale * score P e q h extra j)).le
  · exact le_refl 0

/-! ## Flattening the block sums -/

/-- A sum over `n` blocks of `b` consecutive slots is the sum over `b * n` slots. -/
theorem sum_blocks_range {M : Type*} [AddCommMonoid M] (b n : Nat) (f : Nat → M) :
    (∑ blk ∈ range n, ∑ c ∈ range b, f (blk * b + c)) = ∑ k ∈ range (b * n), f k := by
  rw [show (∑ blk ∈ range n, ∑ c ∈ range b, f (blk * b + c)) =
      ∑ blk ∈ range n, ∑ c ∈ range b, f (b * blk + c) from
    Finset.sum_congr rfl fun blk _ => Finset.sum_congr rfl fun c _ => by
      rw [Nat.mul_comm blk b]]
  exact (sum_range_blocks f b n).symm

/-- A sum over `range N` is the sum over `range L` when the terms above `L` vanish. -/
theorem sum_range_eq_of_ge {M : Type*} [AddCommMonoid M] (f : Nat → M) {L N : Nat}
    (hLN : L ≤ N) (h : ∀ σ, L ≤ σ → f σ = 0) :
    (∑ σ ∈ range N, f σ) = ∑ σ ∈ range L, f σ := by
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hLN) ?_).symm
  intro x _ hx
  have hx' : ¬ x < L := by simpa using hx
  exact h x (by omega)

/-- The main-cache blocks cover the padded main slots `orig_topk_padded`. -/
theorem sum_origBlocks {M : Type*} [AddCommMonoid M] (P : Params) (e : Nat) (f : Nat → M) :
    (∑ τ ∈ range (origBlocks P e), ∑ j ∈ range topkBlock,
        f (τ * topkBlock + j)) =
      ∑ σ ∈ range (origPadded (P.topkLen e)), f σ := by
  rw [sum_blocks_range]
  have hp : topkBlock * origBlocks P e = origPadded (P.topkLen e) := by
    rw [Nat.mul_comm]
    exact numOrigBlocks_mul (P.topkLen e)
  rw [hp]

/-- The extra-cache blocks cover `ceil(extra_topk_length, B_TOPK)` slots. -/
theorem sum_extraBlocks {M : Type*} [AddCommMonoid M] (P : Params) (e : Nat) (f : Nat → M) :
    (∑ τ ∈ range (blocks P e - origBlocks P e), ∑ j ∈ range topkBlock,
        f (τ * topkBlock + j)) =
      ∑ σ ∈ range (ceilToMultiple (P.extraTopkLen e) topkBlock), f σ := by
  rw [sum_blocks_range]
  have hc : blocks P e - origBlocks P e =
      ceilToMultiple (P.extraTopkLen e) topkBlock / topkBlock := by
    rw [blocks_eq, Nat.add_sub_cancel_left]
  have hp : topkBlock *
      (ceilToMultiple (P.extraTopkLen e) topkBlock / topkBlock) =
      ceilToMultiple (P.extraTopkLen e) topkBlock := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr
      (ceilToMultiple_mod (P.extraTopkLen e) topkBlock))
  rw [hc, hp]

/-- The main-padded slot sum is the declared main-cache sum: the weights above the runtime
length are zero. -/
theorem sum_mainBlocks_range {M : Type*} [AddCommMonoid M] (P : Params) (e : Nat)
    (f : Nat → M) (htopk : P.topkLen e ≤ P.topk) (hf : ∀ σ, P.topkLen e ≤ σ → f σ = 0) :
    (∑ τ ∈ range (origBlocks P e), ∑ j ∈ range topkBlock,
        f (τ * topkBlock + j)) = ∑ σ ∈ range P.topk, f σ := by
  refine (sum_origBlocks P e f).trans ?_
  have hpad : P.topkLen e ≤ origPadded (P.topkLen e) :=
    le_trans (le_ceilToMultiple (by decide)) (Nat.le_max_left _ _)
  exact (sum_range_eq_of_ge f hpad hf).trans (sum_range_eq_of_ge f htopk hf).symm

/-- The extra-padded slot sum is the declared extra-cache sum. -/
theorem sum_extraBlocks_range {M : Type*} [AddCommMonoid M] (P : Params) (e : Nat)
    (f : Nat → M) (hextra : P.extraTopkLen e ≤ P.extra_topk)
    (hf : ∀ σ, P.extraTopkLen e ≤ σ → f σ = 0) :
    (∑ τ ∈ range (blocks P e - origBlocks P e), ∑ j ∈ range topkBlock,
        f (τ * topkBlock + j)) = ∑ σ ∈ range P.extra_topk, f σ := by
  refine (sum_extraBlocks P e f).trans ?_
  exact (sum_range_eq_of_ge f (le_ceilToMultiple (by decide)) hf).trans
    (sum_range_eq_of_ge f hextra hf).symm

/-- In the first `origBlocks P e` blocks the block tag is `false` and the slot position is
`τ * B_TOPK + j`. -/
theorem sum_mainBlocks_block {M : Type*} [AddCommMonoid M] (P : Params) (e : Nat)
    (f : Bool → Nat → M) :
    (∑ τ ∈ range (origBlocks P e), ∑ j ∈ range topkBlock,
        f (blockExtra P e τ) (blockSlot P e τ j)) =
      ∑ τ ∈ range (origBlocks P e), ∑ j ∈ range topkBlock,
        f false (τ * topkBlock + j) := by
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [Finset.mem_range] at hτ
  have hb := blockExtra_false (P := P) (e := e) hτ
  simp only [hb, blockSlot_false hb]

/-- In the blocks after the main ones the block tag is `true` and the slot position is
`(τ - origBlocks) * B_TOPK + j`. -/
theorem sum_extraBlocks_block {M : Type*} [AddCommMonoid M] (P : Params) (e : Nat)
    (f : Bool → Nat → M) :
    (∑ τ ∈ range (blocks P e - origBlocks P e), ∑ j ∈ range topkBlock,
        f (blockExtra P e (origBlocks P e + τ)) (blockSlot P e (origBlocks P e + τ) j)) =
      ∑ τ ∈ range (blocks P e - origBlocks P e), ∑ j ∈ range topkBlock,
        f true (τ * topkBlock + j) := by
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
  have hb : blockExtra P e (origBlocks P e + τ) = true := blockExtra_true (Nat.le_add_right _ _)
  simp only [hb, blockSlot_true hb, Nat.add_sub_cancel_left]

/-- **Flattening the block sums.** A sum over the row's blocks, of a per-slot function of the
block's cache tag and position, is the sum over the two caches' index arrays, provided the
function vanishes past each cache's runtime length. -/
theorem sum_blocks_eq {M : Type*} [AddCommMonoid M] (P : Params) (e : Nat)
    (htopk : P.topkLen e ≤ P.topk) (hextra : P.extraTopkLen e ≤ P.extra_topk)
    (f : Bool → Nat → M) (hf : ∀ σ, P.topkLen e ≤ σ → f false σ = 0)
    (he : ∀ σ, P.extraTopkLen e ≤ σ → f true σ = 0) :
    (∑ τ ∈ range (blocks P e), ∑ j ∈ range topkBlock,
        f (blockExtra P e τ) (blockSlot P e τ j)) =
      (∑ σ ∈ range P.topk, f false σ) + ∑ σ ∈ range P.extra_topk, f true σ := by
  have hm : origBlocks P e ≤ blocks P e := origBlocks_le_blocks P e
  rw [(Nat.add_sub_cancel' hm).symm, Finset.sum_range_add]
  change (∑ τ ∈ range (origBlocks P e), ∑ j ∈ range topkBlock,
        f (blockExtra P e τ) (blockSlot P e τ j)) +
      (∑ τ ∈ range (blocks P e - origBlocks P e), ∑ j ∈ range topkBlock,
        f (blockExtra P e (origBlocks P e + τ)) (blockSlot P e (origBlocks P e + τ) j)) =
    (∑ σ ∈ range P.topk, f false σ) + ∑ σ ∈ range P.extra_topk, f true σ
  rw [sum_mainBlocks_block, sum_mainBlocks_range P e (f false) htopk hf,
    sum_extraBlocks_block, sum_extraBlocks_range P e (f true) hextra he]

/-- **The block weights flatten to the row sum.** -/
theorem sum_blockWeight_eq_rowSum (P : Params) (e q h : Nat)
    (htopk : P.topkLen e ≤ P.topk) (hextra : P.extraTopkLen e ≤ P.extra_topk) :
    (∑ τ ∈ range (blocks P e), ∑ j ∈ range topkBlock, blockWeight P e q h τ j) =
      rowSum P e q h := by
  have h := sum_blocks_eq P e htopk hextra (fun extra σ => weight P e q h extra σ)
    (fun σ hσ => weight_false_eq_zero_of_ge hσ)
    (fun σ hσ => weight_true_eq_zero_of_ge hσ)
  simpa [blockWeight, rowSum] using h

/-- **The block weights and values flatten to the numerator.** -/
theorem sum_blockWeight_mul_value_eq_numerator (P : Params) (e q h d : Nat)
    (htopk : P.topkLen e ≤ P.topk) (hextra : P.extraTopkLen e ≤ P.extra_topk) :
    (∑ τ ∈ range (blocks P e), ∑ j ∈ range topkBlock,
        blockWeight P e q h τ j * blockValue P e q τ j d) = numerator P e q h d := by
  have h := sum_blocks_eq P e htopk hextra
    (fun extra σ => weight P e q h extra σ * slotValue P e q extra σ d)
    (fun σ hσ => by rw [weight_false_eq_zero_of_ge hσ, zero_mul])
    (fun σ hσ => by rw [weight_true_eq_zero_of_ge hσ, zero_mul])
  simpa [blockWeight, blockValue, numerator] using h

/-! ## The sink reference -/

/-- The base-2 sink exponent uses the binary32 multiplier compiled from `kernel.cuh:183`.
An absent sink contributes zero weight through `Run.final_noSink`. -/
def sinkLog2 (P : Params) (h : Nat) : ℝ :=
  match P.sink h with
  | some s => s * sinkLog2Factor
  | none => 0

theorem sinkLog2_some {P : Params} {h : Nat} {s : ℝ} (hs : P.sink h = some s) :
    sinkLog2 P h = s * sinkLog2Factor := by
  unfold sinkLog2
  rw [hs]

theorem sinkWeight_some {P : Params} {h : Nat} {s : ℝ} (hs : P.sink h = some s) :
    sinkWeight P h = (2 : ℝ) ^ (s * sinkLog2Factor) := by
  simp [sinkWeight, hs]

/-- Raising two to the compiled sink exponent gives the sink weight. -/
theorem two_rpow_sinkLog2 {P : Params} {h : Nat} {s : ℝ} (hs : P.sink h = some s) :
    (2 : ℝ) ^ sinkLog2 P h = sinkWeight P h := by
  rw [sinkLog2_some hs, sinkWeight_some hs]

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
