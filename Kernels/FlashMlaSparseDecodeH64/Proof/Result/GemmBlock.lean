-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmSums
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Probability
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Wg1Mma MmaDataTrace

noncomputable section

/-- The raw QK dot product of one head and one sparse slot in a block. -/
def blockDot (P : Params) (L : Launch) (g head slot : Nat) (raw : Nat → Nat → Nat) : ℝ :=
  ∑ feature ∈ Finset.range 512,
    P.q (batchOf L g) (queryOf L g) head feature * dequant (raw slot) feature

/-- The contribution computed by one of the two QK datapath halves. -/
def blockHalfDot (P : Params) (L : Launch) (g : Nat) (head slot : Fin 64)
    (half : Fin 2) (raw : Nat → Nat → Nat) : ℝ :=
  let col : Fin 128 := ⟨64 * half.val + slot.val, by omega⟩
  ∑ i ∈ Finset.range 16,
    qkSlice col (P.q (batchOf L g) (queryOf L g) head.val) (dequant (raw slot.val)) i

/-- The two datapath contributions partition the 512 features of the full dot product. -/
theorem blockHalfDot_sum (P : Params) (L : Launch) (g : Nat) (head slot : Fin 64)
    (raw : Nat → Nat → Nat) :
    blockHalfDot P L g head slot 0 raw + blockHalfDot P L g head slot 1 raw =
      blockDot P L g head.val slot.val raw := by
  let f := P.q (batchOf L g) (queryOf L g) head.val
  let k := dequant (raw slot.val)
  have hSplit := qk_add_halves slot f k
  rw [Fin.sum_univ_eq_sum_range (fun j : Nat => f j * k j)] at hSplit
  simpa only [blockHalfDot, blockDot, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one,
    Nat.zero_add, f, k] using hSplit

/-- Only valid slots contribute to the block's online softmax. -/
def blockScore (P : Params) (L : Launch) (g head slot : Nat) (raw : Nat → Nat → Nat)
    (valid : Nat → Bool) : WithBot ℝ :=
  if valid slot then (↑(blockDot P L g head slot raw) : WithBot ℝ) else ⊥

/-- The QK evidence for one particular block consists of its actual issue sequence,
the operand bytes and the previous partial-sum writer of each accumulating issue. -/
structure BlockQkInputs (P : Params) (L : Launch) (X : Execution) (g block : Nat)
    (raw : Nat → Nat → Nat) where
  event : Fin 16 → EvId
  operands : Fin 16 → AsyncCopy.MmaOperands
  issue : ∀ i, X.MmaIssue (event i) tmemP (qkOperands L g block i) (qkAccum i) [0, 0, 0, 0]
  observed : ∀ i, X.async.mmaOperands (event i) = some (operands i)
  query : ∀ (i : Fin 16) (head : Fin 64) (col : Fin 128),
    Bf16Operand (operands i).a (head.val + 64 * (col.val / 64)) fun k =>
      P.q (batchOf L g) (queryOf L g) head.val (qkDepthAt col i.val k)
  key : ∀ (i : Fin 16) (col : Fin 128), Bf16Operand (operands i).b col.val fun k =>
    dequant (raw (col.val % 64)) (qkDepthAt col i.val k)
  previous : ∀ (i : Nat) (hi : i + 1 < 16) (head : Fin 64) (col : Fin 128),
    TcMma.ReadSource L X .acc (event ⟨i, by omega⟩) (event ⟨i + 1, hi⟩)
      ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩

/-- The actual final QK cell contains the explicit dot contribution for its datapath half. -/
theorem qk_block_halves {P : Params} {L : Launch} {X : Execution} {g block : Nat}
    {raw : Nat → Nat → Nat} (ht : AsyncCopy.TcEffectsOk X)
    (inputs : BlockQkInputs P L X g block raw) (head slot : Fin 64) :
    TcMma.Result L Assumptions.all X (inputs.event 15)
        ⟨ctaOf L g, head.val, tmemP + slot.val⟩
        (.float .f32 (blockHalfDot P L g head slot 0 raw)) ∧
      TcMma.Result L Assumptions.all X (inputs.event 15)
        ⟨ctaOf L g, head.val + 64, tmemP + slot.val⟩
        (.float .f32 (blockHalfDot P L g head slot 1 raw)) := by
  let low : Fin 128 := ⟨slot.val, by omega⟩
  let high : Fin 128 := ⟨64 + slot.val, by omega⟩
  have hlow : low.val % 64 = slot.val := Nat.mod_eq_of_lt slot.isLt
  have hhigh : high.val % 64 = slot.val := by dsimp [high]; omega
  have hdlo : low.val / 64 = 0 := Nat.div_eq_of_lt slot.isLt
  have hdhi : high.val / 64 = 1 := by dsimp [high]; omega
  let query := P.q (batchOf L g) (queryOf L g) head.val
  let key := dequant (raw slot.val)
  have hm (col : Fin 128) (hmod : col.val % 64 = slot.val) :
      TcMma.Result L Assumptions.all X (inputs.event 15)
        ⟨ctaOf L g, head.val + 64 * (col.val / 64), tmemP + col.val % 64⟩
        (.float .f32 (∑ j ∈ Finset.range 16, qkSlice col query key j)) := by
    apply qk_half_result (P := P) ht inputs.event inputs.operands inputs.issue inputs.observed
      head col key (fun i => inputs.query i head col) ?_ (fun i n => inputs.previous i n head col)
    intro i
    have he := inputs.key i col
    rw [hmod] at he
    exact he
  constructor
  · have he := hm low hlow
    rw [hlow, hdlo] at he
    simpa only [blockHalfDot, low, query, key, Fin.val_zero, Nat.mul_zero,
      Nat.zero_add, Nat.add_zero] using he
  · have he := hm high hhigh
    rw [hhigh, hdhi] at he
    simpa only [blockHalfDot, high, query, key, Fin.val_one, Nat.mul_one] using he

/-- The stored probability for a sparse slot is its masked weight at the block's reference. -/
def blockProbability (P : Params) (L : Launch) (g head : Nat) (ref : ℝ)
    (raw : Nat → Nat → Nat) (valid : Nat → Bool) (slot : Nat) : ℝ :=
  shiftedWeight P.scale ref (blockScore P L g head slot raw valid)

/-- The PV evidence for one block identifies the eight actual issues, the probability and
dequantized cache bytes they read, and the preceding writer of each accumulating slice. -/
structure BlockPvInputs (P : Params) (L : Launch) (X : Execution) (g block : Nat)
    (raw : Nat → Nat → Nat) (valid : Nat → Bool) (ref : Nat → ℝ) where
  event : Fin 8 → EvId
  operands : Fin 8 → AsyncCopy.MmaOperands
  issue : ∀ i, X.MmaIssue (event i) (pvDest i) (pvOperands L g block i) (pvAccum block i)
    [0, 0, 0, 0]
  observed : ∀ i, X.async.mmaOperands (event i) = some (operands i)
  probability : ∀ (i : Fin 8) (head : Fin 64) (col : Fin 256),
    Bf16Operand (operands i).a (head.val + 64 * (col.val / 128)) fun k =>
      blockProbability P L g head.val (ref head.val) raw valid (16 * (i.val / 2) + k)
  value : ∀ (i : Fin 8) (col : Fin 256), Bf16Operand (operands i).b col.val fun k =>
    dequant (raw (16 * (i.val / 2) + k)) (pvFeature i col)
  previous : ∀ (i : Nat) (hi : i + 1 < 4) (half : Fin 2) (head : Fin 64) (col : Fin 256),
    TcMma.ReadSource L X .acc (event (pvHalfIssue half ⟨i, by omega⟩))
      (event (pvHalfIssue half ⟨i + 1, hi⟩))
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩

/-- For each head and feature, PV adds this block's weighted value to the rescaled old
accumulator. The seed witness supplies either a fresh zero or the actual old-D source. -/
theorem pv_block_update {P : Params} {L : Launch} {X : Execution} {g block : Nat}
    {raw : Nat → Nat → Nat} {valid : Nat → Bool} {ref : Nat → ℝ}
    (ht : AsyncCopy.TcEffectsOk X) (inputs : BlockPvInputs P L X g block raw valid ref)
    (head : Fin 64) (half : Fin 2) (col : Fin 256) (prior gain : ℝ)
    (seed : GemmAccumulator L X (inputs.event (pvHalfIssue half 0))
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (pvAccum block (pvHalfIssue half 0)) (prior * gain)) :
    TcMma.Result L Assumptions.all X (inputs.event (pvHalfIssue half 3))
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (.float .f32 (prior * gain + ∑ slot ∈ Finset.range 64,
        blockProbability P L g head.val (ref head.val) raw valid slot *
          dequant (raw slot) (256 * half.val + col.val))) := by
  let weight := blockProbability P L g head.val (ref head.val) raw valid
  let value := fun slot feature => dequant (raw slot) feature
  have hhalf (i : Fin 4) : (pvHalfIssue half i).val % 2 = half.val := by
    change (2 * i.val + half.val) % 2 = half.val
    omega
  have hpart (i : Fin 4) : (pvHalfIssue half i).val / 2 = i.val := by
    change (2 * i.val + half.val) / 2 = i.val
    omega
  have ha (i : Fin 4) : Bf16Operand (inputs.operands (pvHalfIssue half i)).a
      (head.val + 64 * (col.val / 128)) fun k => weight (16 * i.val + k) := by
    have he := inputs.probability (pvHalfIssue half i) head col
    rwa [hpart] at he
  have hb (i : Fin 4) : Bf16Operand (inputs.operands (pvHalfIssue half i)).b col.val fun k =>
      value (16 * i.val + k) (256 * half.val + col.val) := by
    have he := inputs.value (pvHalfIssue half i) col
    rwa [hpart, pvFeature, hhalf] at he
  have he := pv_half_result ht half (fun i => inputs.event (pvHalfIssue half i))
    (fun i => inputs.operands (pvHalfIssue half i)) (fun i => inputs.issue _) (fun i =>
      inputs.observed (pvHalfIssue half i)) head col weight value ha hb seed
    (fun i h => inputs.previous i h half head col)
  rw [Fin.sum_univ_eq_sum_range (fun k => weight k * value k (256 * half.val + col.val))] at he
  rw [add_comm (prior * gain)]
  exact he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
