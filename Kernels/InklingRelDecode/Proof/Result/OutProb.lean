-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutRow

@[expose] public section

/-!
# The probabilities and rescale factors of the softmax, and the final O accumulator

`MmaRun.oFull_eq_run` says that the O accumulator is the numerator of `Softmax.run` when the
probabilities the softmax stored in Tensor Memory are `Softmax.step`'s `p_k` on a visible key and
`0` on a masked one, and the rescale factors are `Softmax.step`'s `alpha`. This file states those
two functions in `Spec`'s terms for the row of a tile row `r` of a thread's CTA (`pElemE`,
`alphaE`: the premises `PTile` and `OAcc` of the MMA data path are taken for exactly these), and
instantiates `oFull_eq_run`:

* `mUseOf` and `alphaOf` depend on the scores only (`mUse_congr`, `alpha_congr`), so the functions
  are defined from the value-free blocks and hold for every output column;
* `oFull_last`: after the last block the O accumulator of column `n` is the numerator `o` of
  `colState`, the state `Softmax.run` reaches over the blocks of the output column.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Softmax (St)
open Classical

noncomputable section

/-! ### The softmax's probabilities and rescale factors of a row -/

/-- The factor the softmax applies to the state before block `b`, from the scores alone. -/
def alphaE (P : Params) (r s tok head b : Nat) : ℝ :=
  alphaOf (sl P) (blk P r s tok head (fun _ _ => 0) b)
    (before (sl P) (blk P r s tok head (fun _ _ => 0)) b)

/-- The reference maximum `m_use` of block `b`, from the scores alone. -/
def muE (P : Params) (r s tok head b : Nat) : ℝ :=
  mUseOf (sl P) (blk P r s tok head (fun _ _ => 0) b)
    (before (sl P) (blk P r s tok head (fun _ _ => 0)) b)

/-- The probability of key `k` of block `b`: `2 ^ (sl · logit − m_use · sl)` for a visible key,
`0` for a masked one. -/
def probE (P : Params) (r s tok head b k : Nat) : ℝ :=
  if Vis P r s tok b k then
    (2 : ℝ) ^ (sl P * logit P r s tok head b k - muE P r s tok head b * sl P)
  else 0

/-- The probability in tile row `r` of thread `g`'s CTA (token `r / 6`, head `6 kvh + r % 6`). -/
def pElemE (Q : Params) (L : Launch) (g r b k : Nat) : ℝ :=
  probE Q (reqOf L g) (splitOf L g) (r / 6) (group * kvhOf L g + r % 6) b k

/-- The rescale factor before block `b` in tile row `r` of thread `g`'s CTA. -/
def alphaRow (Q : Params) (L : Launch) (g b r : Nat) : ℝ :=
  alphaE Q (reqOf L g) (splitOf L g) (r / 6) (group * kvhOf L g + r % 6) b

/-! ### The scores alone decide them -/

theorem before_ml_congr (P : Params) (r s tok head : Nat) (vv : Nat → Nat → ℝ) (b : Nat) :
    (before (sl P) (blk P r s tok head vv) b).m =
      (before (sl P) (blk P r s tok head (fun _ _ => 0)) b).m := by
  unfold before
  refine (run_ml_congr (sl P) ?_).1
  simp only [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  exact blk_fst P r s tok head vv _ x

theorem alpha_congr (P : Params) (r s tok head : Nat) (vv : Nat → Nat → ℝ) (b : Nat) :
    alphaOf (sl P) (blk P r s tok head vv b) (before (sl P) (blk P r s tok head vv) b) =
      alphaE P r s tok head b := by
  unfold alphaE alphaOf
  rw [before_ml_congr P r s tok head vv b, blockMax_congr (blk_fst P r s tok head vv _ b)]

theorem mUse_congr (P : Params) (r s tok head : Nat) (vv : Nat → Nat → ℝ) (b : Nat) :
    mUseOf (sl P) (blk P r s tok head vv b) (before (sl P) (blk P r s tok head vv) b) =
      muE P r s tok head b := by
  unfold muE mUseOf
  rw [before_ml_congr P r s tok head vv b, blockMax_congr (blk_fst P r s tok head vv _ b)]

/-! ### The O accumulator after the last block -/

variable {Q : Params} {L : Launch}

/-- The blocks of tile row `r` of thread `g`'s CTA at column `n`, as `Mma` sees them, are the
blocks of `Spec`'s row: the V element is the cache's, the key is `128 · block + k`. -/
theorem vElem_eq (g r n : Nat) :
    (fun b k => vElem Q L g b k n) =
      val Q (reqOf L g) (splitOf L g) (group * kvhOf L g + r % 6) n := by
  funext b k
  have hh : (group * kvhOf L g + r % 6) / group = kvhOf L g := by
    unfold group
    omega
  unfold vElem val key blkOf
  rw [hh]

theorem blockOf_eq (g r n : Nat) :
    blockOf (Vis Q (reqOf L g) (splitOf L g) (r / 6))
      (logit Q (reqOf L g) (splitOf L g) (r / 6) (group * kvhOf L g + r % 6))
      (fun b k => vElem Q L g b k n) =
      blk Q (reqOf L g) (splitOf L g) (r / 6) (group * kvhOf L g + r % 6)
        (val Q (reqOf L g) (splitOf L g) (group * kvhOf L g + r % 6) n) := by
  funext b
  rw [vElem_eq g r n]
  rfl

/-- **The O accumulator after block `b` is the numerator of the row's softmax run.** For tile row
`r` and column `n` of thread `g`'s CTA, `oFull` for the probabilities `pElemE` and the factors
`alphaRow` is the numerator `o` of `Softmax.run` over the blocks `0 … b` of output column `n`. -/
theorem oFull_eq_colRun (g r n : Nat) (b : Nat) :
    oFull (pElemE Q L) (alphaRow Q L) Q L g r n b =
      (Softmax.run (sl Q) ((List.range (b + 1)).map (blk Q (reqOf L g) (splitOf L g) (r / 6)
        (group * kvhOf L g + r % 6) (val Q (reqOf L g) (splitOf L g)
          (group * kvhOf L g + r % 6) n)))).o := by
  have h := oFull_eq_run (pElemE Q L) (alphaRow Q L) Q L g r n (sl Q)
    (Vis Q (reqOf L g) (splitOf L g) (r / 6))
    (logit Q (reqOf L g) (splitOf L g) (r / 6) (group * kvhOf L g + r % 6))
    (fun b k _ hv => by
      rw [blockOf_eq g r n, mUse_congr]
      simp only [pElemE, probE, hv, ↓reduceIte, muE])
    (fun b k _ hv => by simp [pElemE, probE, hv])
    (fun b _ => by
      rw [blockOf_eq g r n]
      unfold alphaRow
      rw [← alpha_congr Q (reqOf L g) (splitOf L g) (r / 6) (group * kvhOf L g + r % 6)
        (val Q (reqOf L g) (splitOf L g) (group * kvhOf L g + r % 6) n) b]) b
  rw [h, blockOf_eq g r n]

/-- **After the last block** (`num_iters = b + 1`) the O accumulator is `colState`'s numerator. -/
theorem oFull_last (g r n b : Nat)
    (hN : Q.numIters (reqOf L g) (splitOf L g) = b + 1) :
    oFull (pElemE Q L) (alphaRow Q L) Q L g r n b =
      (colState Q (reqOf L g) (splitOf L g) (r / 6) (group * kvhOf L g + r % 6) n).o := by
  rw [oFull_eq_colRun g r n b]
  unfold colState blocksD blocks
  rw [hN]

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
