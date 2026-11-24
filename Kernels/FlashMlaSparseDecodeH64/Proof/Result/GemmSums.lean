-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmResults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmPartition
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Wg1Mma MmaDataTrace

noncomputable section

/-- The contraction feature of a given QK datapath column and issue. -/
def qkDepthAt (col : Fin 128) (issue k : Nat) : Nat :=
  128 * (issue / 4) + 64 * (col.val / 64) + 16 * (issue % 4) + k

/-- One contribution to the accumulator of a QK score half. -/
def qkSlice (col : Fin 128) (query key : Nat → ℝ) (i : Nat) : ℝ :=
  ∑ k ∈ Finset.range 16, query (qkDepthAt col i k) * key (qkDepthAt col i k)

/-- The final accumulator for one QK half has exactly its sixteen issue contributions. -/
theorem qk_half_result {P : Params} {L : Launch} {g block : Nat} {X : Execution}
    (ht : AsyncCopy.TcEffectsOk X) (events : Fin 16 → EvId) (ops : Fin 16 → AsyncCopy.MmaOperands)
    (hi : ∀ i, X.MmaIssue (events i) tmemP (qkOperands L g block i) (qkAccum i) [0, 0, 0, 0])
    (ho : ∀ i, X.async.mmaOperands (events i) = some (ops i))
    (row : Fin 64) (col : Fin 128) (key : Nat → ℝ)
    (ha : ∀ i, Bf16Operand (ops i).a (row.val + 64 * (col.val / 64)) fun k =>
      P.q (batchOf L g) (queryOf L g) row.val (qkDepthAt col i.val k))
    (hb : ∀ i, Bf16Operand (ops i).b col.val fun k => key (qkDepthAt col i.val k))
    (hs : ∀ (i : Nat) (h : i + 1 < 16), TcMma.ReadSource L X .acc
      (events ⟨i, by omega⟩) (events ⟨i + 1, h⟩)
      ⟨ctaOf L g, row.val + 64 * (col.val / 64), tmemP + col.val % 64⟩) :
    TcMma.Result L Assumptions.all X (events 15)
      ⟨ctaOf L g, row.val + 64 * (col.val / 64), tmemP + col.val % 64⟩
      (.float .f32 (∑ i ∈ Finset.range 16,
        qkSlice col (P.q (batchOf L g) (queryOf L g) row.val) key i)) := by
  let cell : TcMma.Cell := ⟨ctaOf L g, row.val + 64 * (col.val / 64), tmemP + col.val % 64⟩
  let chunk := qkSlice col (P.q (batchOf L g) (queryOf L g) row.val) key
  have hresult (i : Nat) (h : i < 16) :
      TcMma.Result L Assumptions.all X (events ⟨i, h⟩) cell
        (.float .f32 (∑ j ∈ Finset.range (i + 1), chunk j)) := by
    induction i with
    | zero =>
      have hacc : GemmAccumulator L X (events 0) cell (qkAccum 0) 0 := .overwrite
      have he := qk_chunk_result ht (hi 0) (ho 0) row col key (ha 0) (hb 0) hacc
      change TcMma.Result L Assumptions.all X (events 0) cell
        (.float .f32 (chunk 0 + 0)) at he
      rw [Nat.zero_add, Finset.sum_range_one]
      rw [add_zero] at he
      exact he
    | succ i ih =>
      let j : Fin 16 := ⟨i + 1, h⟩
      let sum := ∑ k ∈ Finset.range (i + 1), chunk k
      have hac : qkAccum j = true := by simp [qkAccum, j]
      have hprev := ih (by omega)
      have hacc : GemmAccumulator L X (events j) cell (qkAccum j) sum := by
        rw [hac]
        exact .priorMma (hs i h) hprev
      have he := qk_chunk_result ht (hi j) (ho j) row col key (ha j) (hb j) hacc
      change TcMma.Result L Assumptions.all X (events j) cell
        (.float .f32 (chunk (i + 1) + sum)) at he
      rw [Finset.sum_range_succ (n := i + 1)]
      change TcMma.Result L Assumptions.all X (events j) cell
        (.float .f32 (sum + chunk (i + 1)))
      rw [add_comm]
      exact he
  exact hresult 15 (by decide)

/-- Adding the two datapath results recovers the full 512-feature QK dot product. -/
theorem qk_add_halves (col : Fin 64) (query key : Nat → ℝ) :
    let lo : Fin 128 := ⟨col.val, by omega⟩
    let hi : Fin 128 := ⟨64 + col.val, by omega⟩
    (∑ i ∈ Finset.range 16, qkSlice lo query key i) +
      (∑ i ∈ Finset.range 16, qkSlice hi query key i) =
      ∑ k : Fin 512, query k.val * key k.val := by
  dsimp only
  have hlo : col.val / 64 = 0 := Nat.div_eq_of_lt col.isLt
  have hhi : (64 + col.val) / 64 = 1 := by omega
  let f (half : Nat) (i k : Nat) :=
    query (128 * (i / 4) + 64 * half + 16 * (i % 4) + k) *
      key (128 * (i / 4) + 64 * half + 16 * (i % 4) + k)
  change (∑ i ∈ Finset.range 16, ∑ k ∈ Finset.range 16, f (col.val / 64) i k) +
    (∑ i ∈ Finset.range 16, ∑ k ∈ Finset.range 16, f ((64 + col.val) / 64) i k) = _
  rw [hlo, hhi]
  have he := qk_sum (fun j => query j.val * key j.val)
  simp only [← Fin.sum_univ_eq_sum_range]
  simpa [Fin.sum_univ_two, qkDepth, f] using he

/-- Each PV destination receives the four alternating issues for its output half. -/
def pvHalfIssue (half : Fin 2) (part : Fin 4) : Fin 8 :=
  ⟨2 * part.val + half.val, by omega⟩

/-- One weighted value slice for a fixed logical output feature. -/
def pvSlice (weight : Nat → ℝ) (value : Nat → Nat → ℝ) (feature part : Nat) : ℝ :=
  ∑ k ∈ Finset.range 16, weight (16 * part + k) * value (16 * part + k) feature

private theorem pvHalfIssue_part (half : Fin 2) (part : Fin 4) :
    (pvHalfIssue half part).val / 2 = part.val := by
  change (2 * part.val + half.val) / 2 = part.val
  omega

private theorem pvHalfIssue_half (half : Fin 2) (part : Fin 4) :
    (pvHalfIssue half part).val % 2 = half.val := by
  change (2 * part.val + half.val) % 2 = half.val
  omega

private theorem pvHalfIssue_cell (half : Fin 2) (part : Fin 4) :
    pvDest (pvHalfIssue half part) = tmemO + 128 * half.val := by
  rw [pvDest, pvHalfIssue_half]

/-- With an observed initial accumulator and each preceding slice read, the last PV issue of
one output half writes the complete 64-slot dot product plus that accumulator. -/
theorem pv_half_result {L : Launch} {g block : Nat} {X : Execution}
    (ht : AsyncCopy.TcEffectsOk X) (half : Fin 2) (events : Fin 4 → EvId)
    (ops : Fin 4 → AsyncCopy.MmaOperands)
    (hi : ∀ i, X.MmaIssue (events i) (pvDest (pvHalfIssue half i))
      (pvOperands L g block (pvHalfIssue half i))
      (pvAccum block (pvHalfIssue half i)) [0, 0, 0, 0])
    (ho : ∀ i, X.async.mmaOperands (events i) = some (ops i))
    (row : Fin 64) (col : Fin 256) (weight : Nat → ℝ) (value : Nat → Nat → ℝ)
    (ha : ∀ i, Bf16Operand (ops i).a (row.val + 64 * (col.val / 128)) fun k =>
      weight (16 * i.val + k))
    (hb : ∀ i, Bf16Operand (ops i).b col.val fun k =>
      value (16 * i.val + k) (256 * half.val + col.val))
    {seed : ℝ}
    (hseed : GemmAccumulator L X (events 0)
      ⟨ctaOf L g, row.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (pvAccum block (pvHalfIssue half 0)) seed)
    (hs : ∀ (i : Nat) (h : i + 1 < 4), TcMma.ReadSource L X .acc
      (events ⟨i, by omega⟩) (events ⟨i + 1, h⟩)
      ⟨ctaOf L g, row.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩) :
    TcMma.Result L Assumptions.all X (events 3)
      ⟨ctaOf L g, row.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
      (.float .f32 ((∑ k : Fin 64, weight k.val * value k.val (256 * half.val + col.val)) +
        seed)) := by
  let cell : TcMma.Cell :=
    ⟨ctaOf L g, row.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
  let feature := 256 * half.val + col.val
  let chunk := pvSlice weight value feature
  have one (i : Fin 4) (prev : ℝ)
      (hacc : GemmAccumulator L X (events i) cell (pvAccum block (pvHalfIssue half i)) prev) :
      TcMma.Result L Assumptions.all X (events i) cell (.float .f32 (chunk i.val + prev)) := by
    let part := pvHalfIssue half i
    have ha' : Bf16Operand (ops i).a (row.val + 64 * (col.val / 128)) fun k =>
        weight (16 * (part.val / 2) + k) := by
      rw [pvHalfIssue_part]
      exact ha i
    have hb' : Bf16Operand (ops i).b col.val fun k =>
        value (16 * (part.val / 2) + k) (pvFeature part col) := by
      rw [pvHalfIssue_part, pvFeature, pvHalfIssue_half]
      exact hb i
    have hacc' : GemmAccumulator L X (events i)
        ⟨ctaOf L g, row.val + 64 * (col.val / 128), pvDest part + col.val % 128⟩
        (pvAccum block part) prev := by
      rw [pvHalfIssue_cell]
      exact hacc
    have hx := pv_chunk_result ht (hi i) (ho i) row col weight value ha' hb' hacc'
    rw [pvHalfIssue_cell, pvHalfIssue_part, pvFeature, pvHalfIssue_half] at hx
    exact hx
  have hresult (i : Nat) (h : i < 4) :
      TcMma.Result L Assumptions.all X (events ⟨i, h⟩) cell
        (.float .f32 ((∑ j ∈ Finset.range (i + 1), chunk j) + seed)) := by
    induction i with
    | zero =>
      rw [Nat.zero_add, Finset.sum_range_one]
      exact one 0 seed hseed
    | succ i ih =>
      let j : Fin 4 := ⟨i + 1, h⟩
      let sum := ∑ k ∈ Finset.range (i + 1), chunk k
      have hac : pvAccum block (pvHalfIssue half j) = true := by
        have hlt : 2 ≤ (pvHalfIssue half j).val := by
          change 2 ≤ 2 * (i + 1) + half.val
          omega
        simp [pvAccum, hlt]
      have hp : GemmAccumulator L X (events j) cell (pvAccum block (pvHalfIssue half j))
          (sum + seed) := by
        rw [hac]
        exact .priorMma (hs i h) (ih (by omega))
      have he := one j (sum + seed) hp
      rw [Finset.sum_range_succ (n := i + 1)]
      change TcMma.Result L Assumptions.all X (events j) cell
        (.float .f32 ((sum + chunk (i + 1)) + seed))
      rw [add_comm sum, add_assoc]
      exact he
  have hsum : (∑ j ∈ Finset.range 4, chunk j) =
      ∑ k : Fin 64, weight k.val * value k.val feature := by
    have he := pv_sum (fun j => weight j.val * value j.val feature)
    simp only [chunk, pvSlice, ← Fin.sum_univ_eq_sum_range]
    simpa [finProdFinEquiv, Nat.add_comm] using he
  change TcMma.Result L Assumptions.all X (events 3) cell
    (.float .f32 ((∑ k : Fin 64, weight k.val * value k.val feature) + seed))
  rw [← hsum]
  exact hresult 3 (by decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
