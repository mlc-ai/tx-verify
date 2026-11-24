-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaO
public import Kernels.InklingRelDecode.Proof.Result.Softmax

@[expose] public section

/-!
# The O accumulator is the online softmax's numerator

`MmaO.lean` leaves the O cell after block `b` as `oFull b`, the `alpha`-rescaled running sum of
`P · V` (`oFull (b + 1) = alpha (b + 1) · oFull b + Σ_{kk < 128} P(b + 1, kk) · V(b + 1, kk, n)`).
The kernel's online softmax (`Softmax.step`, `Proof/Result/Softmax.lean`) keeps, for a column `n`,
the running numerator `o` with `o' = o · alpha + Σ_{visible keys} p_k · v_k`, where its `alpha` and
`p_k = 2 ^ (scale_log2 · s_k − m_use · scale_log2)` are functions of the state before the block.
This file shows the two agree, with the softmax's own definitions:

* `alphaOf`, `mUseOf`: the `alpha` and `m_use` of `Softmax.step`, and `step_o`:
  `(Softmax.step sl blk st).o = st.o · alphaOf + Σ p_q · v_q` (`rfl`);
* `blockOf`: the visible keys of block `b` of the row as `(logit, value)` pairs, `before`: the
  state before it;
* `oFull_eq_run`: if the stored probabilities are the softmax's `p_k` on the visible keys and `0`
  on the others (the masked keys have weight 0), and the rescale factors are `alphaOf` of the state
  before each block (the premise on the default partition: its `alpha`, as the `OAcc.base` store
  or the lazy skip with `alphaOf = 1`), then
  `oFull b = (Softmax.run sl [block 0, …, block b]).o`.

So the exact content of the O cell is `Softmax.run`'s numerator `o`, and `Softmax.fold_invariant`
turns that into `Σ W v` relative to the running maximum.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX
open PTX.Kernels.InklingRelDecode.Softmax (Keep alphaLog2 blockMax mSafe pow2)

noncomputable section

open Classical

/-! ### The softmax's `alpha` and `m_use` -/

/-- The factor `alpha` by which `Softmax.step` rescales the old state against the block `blk`
(`1` when the rescale is lazy, `2 ^ alpha_log2` otherwise). -/
def alphaOf (sl : ℝ) (blk : List (ℝ × ℝ)) (st : Softmax.St) : ℝ :=
  if Keep (alphaLog2 sl st.m (max st.m (blockMax blk))) then 1
  else pow2 (alphaLog2 sl st.m (max st.m (blockMax blk)))

/-- The reference maximum `m_use` of `Softmax.step` against the block `blk`. -/
def mUseOf (sl : ℝ) (blk : List (ℝ × ℝ)) (st : Softmax.St) : ℝ :=
  if Keep (alphaLog2 sl st.m (max st.m (blockMax blk))) then st.m.toReal
  else mSafe (max st.m (blockMax blk))

/-- **The numerator of one step**: the old numerator times `alpha` plus the sum of `p_k · v_k`. -/
theorem step_o (sl : ℝ) (blk : List (ℝ × ℝ)) (st : Softmax.St) :
    (Softmax.step sl blk st).o = st.o * alphaOf sl blk st +
      (blk.map fun q => (2 : ℝ) ^ (sl * q.1 - mUseOf sl blk st * sl) * q.2).sum := by
  unfold Softmax.step alphaOf mUseOf
  rfl

/-- A run over one more block is a step. -/
theorem run_snoc (sl : ℝ) (l : List (List (ℝ × ℝ))) (x : List (ℝ × ℝ)) :
    Softmax.run sl (l ++ [x]) = Softmax.step sl x (Softmax.run sl l) := by
  unfold Softmax.run
  rw [List.foldl_append]
  rfl

/-! ### The blocks of a row -/

/-- The visible keys of block `b`, as `(score, value)` pairs in key order: `sc b k` is the score
term of key `k` of block `b` and `vv b k` its value at the column. -/
def blockOf (vis : Nat → Nat → Prop) (sc vv : Nat → Nat → ℝ) (b : Nat) : List (ℝ × ℝ) :=
  ((List.range 128).filter fun k => decide (vis b k)).map fun k => (sc b k, vv b k)

/-- The softmax state before block `b`. -/
def before (sl : ℝ) (blk : Nat → List (ℝ × ℝ)) (b : Nat) : Softmax.St :=
  Softmax.run sl ((List.range b).map blk)

theorem run_succ (sl : ℝ) (blk : Nat → List (ℝ × ℝ)) (b : Nat) :
    Softmax.run sl ((List.range (b + 1)).map blk) = Softmax.step sl (blk b) (before sl blk b) := by
  rw [List.range_succ, List.map_append, List.map_singleton, run_snoc]
  rfl

/-- **The PV sum of a block is the sum over its visible keys** when the probabilities are the
softmax's on the visible keys and zero on the rest. -/
theorem sum_blockOf (sl : ℝ) (vis : Nat → Nat → Prop) (sc vv p : Nat → Nat → ℝ) (b : Nat)
    (mu : ℝ) (hp : ∀ k, k < 128 → vis b k → p b k = (2 : ℝ) ^ (sl * sc b k - mu * sl))
    (hp0 : ∀ k, k < 128 → ¬ vis b k → p b k = 0) :
    (∑ k ∈ Finset.range 128, p b k * vv b k) =
      ((blockOf vis sc vv b).map fun q => (2 : ℝ) ^ (sl * q.1 - mu * sl) * q.2).sum := by
  have h1 : (∑ k ∈ Finset.range 128, p b k * vv b k) =
      ∑ k ∈ (Finset.range 128).filter (vis b), (2 : ℝ) ^ (sl * sc b k - mu * sl) * vv b k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    by_cases hv : vis b k
    · simp [hv, hp k hk' hv]
    · simp [hv, hp0 k hk' hv]
  rw [h1, blockOf, List.map_map]
  have hnd : ((List.range 128).filter fun k => decide (vis b k)).Nodup :=
    (List.nodup_range).filter _
  rw [← List.sum_toFinset _ hnd]
  have hset : ((List.range 128).filter fun k => decide (vis b k)).toFinset =
      (Finset.range 128).filter (vis b) := by
    ext k
    simp
  rw [hset]
  rfl

/-- **The O accumulator is the online softmax's numerator.** For the row `r` and column `n` of
thread `g`'s CTA, with `sc b k` the score term of key `k` of block `b` and `vis b k` its
visibility: if the stored probability is the softmax's `p_k = 2 ^ (sl · s_k − m_use · sl)` on a
visible key (`m_use` of the state before the block) and `0` on a masked one, and the factor applied
before block `b ≥ 1` is `alphaOf` of the state before it, then the accumulator after block `b` is
the numerator `o` of `Softmax.run` over the blocks `0 … b`. -/
theorem oFull_eq_run (pElem : Nat → Nat → Nat → Nat → ℝ) (alpha : Nat → Nat → Nat → ℝ)
    (Q : Params) (L : Launch) (g r n : Nat) (sl : ℝ) (vis : Nat → Nat → Prop)
    (sc : Nat → Nat → ℝ)
    (hp : ∀ b k, k < 128 → vis b k → pElem g r b k = (2 : ℝ) ^ (sl * sc b k -
      mUseOf sl (blockOf vis sc (fun b k => vElem Q L g b k n) b)
        (before sl (blockOf vis sc (fun b k => vElem Q L g b k n)) b) * sl))
    (hp0 : ∀ b k, k < 128 → ¬ vis b k → pElem g r b k = 0)
    (hal : ∀ b, 1 ≤ b → alpha g b r =
      alphaOf sl (blockOf vis sc (fun b k => vElem Q L g b k n) b)
        (before sl (blockOf vis sc (fun b k => vElem Q L g b k n)) b)) :
    ∀ b, oFull pElem alpha Q L g r n b =
      (Softmax.run sl ((List.range (b + 1)).map
        (blockOf vis sc (fun b k => vElem Q L g b k n)))).o := by
  set blk := blockOf vis sc (fun b k => vElem Q L g b k n) with hblk
  have hsum : ∀ b, pvPrefix pElem Q L g r b n 128 =
      ((blk b).map fun q => (2 : ℝ) ^ (sl * q.1 - mUseOf sl (blk b) (before sl blk b) * sl) *
        q.2).sum := fun b =>
    sum_blockOf sl vis sc (fun b k => vElem Q L g b k n) (fun b k => pElem g r b k) b _
      (hp b) (hp0 b)
  intro b
  induction b with
  | zero =>
    rw [run_succ, step_o]
    have h0 : (before sl blk 0).o = 0 := by simp [before, Softmax.run]
    rw [h0, zero_mul, zero_add]
    exact hsum 0
  | succ b ih =>
    rw [run_succ, step_o]
    have h1 : (before sl blk (b + 1)).o = oFull pElem alpha Q L g r n b := by
      rw [ih]
      rfl
    rw [h1, ← hsum (b + 1), ← hal (b + 1) (by omega), oFull, mul_comm]

end

end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
