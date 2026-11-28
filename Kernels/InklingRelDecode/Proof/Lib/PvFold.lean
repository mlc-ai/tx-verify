-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftKernel
public import Kernels.InklingRelDecode.Proof.Lib.SoftWords

@[expose] public section

/-! # The accumulator of a row after `n` blocks is the fold's numerator

`clAcc` is the closed form the PV accumulator follows: after block `b` the old value scaled by the
rescale factor `Al b` plus the products of the block's probability words `Pw b` with the values of
the keys. When the words are the fold's (`pExp` of the key relative to `mUseOf`, `0` for the keys
the row does not see) and the factors are the fold's `stepAlpha`, it is the `o` of `kSt n`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow

open Classical SoftFold Finset

/-- The factor the fold's step applies to the old state. -/
noncomputable def stepAlpha (sl : ℝ) (blk : List (ℝ × ℝ)) (st : St) : ℝ :=
  if Keep (alphaLog2 sl st.m (max st.m (blockMax blk))) then 1
  else pow2 (alphaLog2 sl st.m (max st.m (blockMax blk)))

/-- Block `i` of the row, in the kernel's domain. -/
noncomputable def kBlk (P : Params) (r s tok h d i : Nat) : List (ℝ × ℝ) :=
  (blockList P r s tok h d i).map fun q => (q.1 / P.scale, q.2)

/-- The state of the kernel's fold after `n` blocks. -/
noncomputable def kSt (P : Params) (r s tok h d n : Nat) : St :=
  SoftFold.run (P.scale * log2eF32) ((List.range n).map (kBlk P r s tok h d))

/-- The pair of a key in the kernel's domain. -/
noncomputable def keyPair (P : Params) (r tok h d k : Nat) : ℝ × ℝ :=
  ((pair P r tok h d k).1 / P.scale, (pair P r tok h d k).2)

theorem kState_eq (P : Params) (r s tok h d : Nat) :
    kState P r s tok h d = kSt P r s tok h d (P.numIters r s) := by
  simp only [kState, kSt, kBlocks, rowBlocks, List.map_map]
  rfl

theorem kSt_succ (P : Params) (r s tok h d n : Nat) :
    kSt P r s tok h d (n + 1) = step (P.scale * log2eF32) (kBlk P r s tok h d n)
      (kSt P r s tok h d n) := by
  simp [kSt, SoftFold.run, List.range_succ]

theorem kSt_o (P : Params) (r s tok h d n : Nat) :
    (kSt P r s tok h d (n + 1)).o = (kSt P r s tok h d n).o *
      stepAlpha (P.scale * log2eF32) (kBlk P r s tok h d n) (kSt P r s tok h d n) +
      ((kBlk P r s tok h d n).map fun q => pExp (P.scale * log2eF32)
        (mUseOf (P.scale * log2eF32) (kBlk P r s tok h d n) (kSt P r s tok h d n)) q *
          q.2).sum := by
  rw [kSt_succ]
  rfl

theorem kBlk_sum (P : Params) (r s tok h d n : Nat) (G : ℝ × ℝ → ℝ) :
    ((kBlk P r s tok h d n).map G).sum =
      ∑ k ∈ blockKeys P r s tok n, G (keyPair P r tok h d k) := by
  simp only [kBlk, blockList, List.map_map]
  rw [← List.sum_toFinset _ (sort_nodup _ _), sort_toFinset]
  rfl

theorem blockKeys_sub (P : Params) (r s tok n : Nat) :
    blockKeys P r s tok n ⊆ Ico (128 * (P.splits * n + s)) (128 * (P.splits * n + s) + 128) := by
  intro k hk
  simp only [blockKeys, mem_filter] at hk
  have h := hk.2
  rw [mem_Ico]
  have : P.splits * n = n * P.splits := Nat.mul_comm _ _
  omega

/-- The sum over the 128 positions of a block with the words of the keys it has. -/
theorem sum_block (P : Params) (r s tok n : Nat) (g : ℕ → ℝ) :
    ∑ κ ∈ range 128, (if 128 * (P.splits * n + s) + κ ∈ blockKeys P r s tok n then
      g (128 * (P.splits * n + s) + κ) else 0) = ∑ k ∈ blockKeys P r s tok n, g k := by
  have e := Finset.sum_Ico_eq_sum_range
    (fun k => if k ∈ blockKeys P r s tok n then g k else 0) (128 * (P.splits * n + s))
    (128 * (P.splits * n + s) + 128)
  rw [Nat.add_sub_cancel_left] at e
  rw [← e, Finset.sum_ite_mem, Finset.inter_eq_right.2 (blockKeys_sub P r s tok n)]

/-- The closed form of the accumulator: block `b` adds its products to the rescaled old value. -/
noncomputable def clAcc (V : ℕ → ℝ) (Pw : ℕ → ℕ → ℝ) (Al : ℕ → ℝ) (sp x : Nat) : ℕ → ℝ
  | 0 => 0
  | b + 1 => (∑ κ ∈ range 128, Pw b κ * V (128 * (sp * b + x) + κ)) + Al b * clAcc V Pw Al sp x b

/-- **The closed form is the fold's numerator**, for words and factors that are the fold's. -/
theorem clAcc_eq (P : Params) (r s tok h d : Nat) {Pw : ℕ → ℕ → ℝ} {Al : ℕ → ℝ} :
    ∀ n, (∀ b < n, ∀ κ < 128, Pw b κ =
      if 128 * (P.splits * b + s) + κ ∈ blockKeys P r s tok b then
        pExp (P.scale * log2eF32) (mUseOf (P.scale * log2eF32) (kBlk P r s tok h d b)
          (kSt P r s tok h d b)) (keyPair P r tok h d (128 * (P.splits * b + s) + κ)) else 0) →
    (∀ b < n, Al b = stepAlpha (P.scale * log2eF32) (kBlk P r s tok h d b)
      (kSt P r s tok h d b)) →
    clAcc (fun k => (keyPair P r tok h d k).2) Pw Al P.splits s n = (kSt P r s tok h d n).o := by
  intro n
  induction n with
  | zero => intro _ _; simp [clAcc, kSt, SoftFold.run]
  | succ n ih =>
    intro hp ha
    rw [clAcc, kSt_o, ih (fun b hb => hp b (by omega)) (fun b hb => ha b (by omega)),
      ha n (by omega), kBlk_sum]
    have hs : ∑ κ ∈ range 128, Pw n κ * (keyPair P r tok h d (128 * (P.splits * n + s) + κ)).2 =
        ∑ k ∈ blockKeys P r s tok n, pExp (P.scale * log2eF32) (mUseOf (P.scale * log2eF32)
          (kBlk P r s tok h d n) (kSt P r s tok h d n)) (keyPair P r tok h d k) *
            (keyPair P r tok h d k).2 := by
      rw [← sum_block P r s tok n]
      refine sum_congr rfl fun κ hκ => ?_
      rw [hp n (by omega) κ (mem_range.1 hκ)]
      split_ifs <;> simp
    rw [hs]
    ring

end PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow
