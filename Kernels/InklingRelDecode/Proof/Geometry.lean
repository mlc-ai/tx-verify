-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-!
# Geometry and split arithmetic of the Inkling relative decode kernel

Facts about the specification's `Params` and `Pre` that the proof uses and that need no execution:
the tensor map is valid, the relative-logit column of a key is in range, the splits partition the
key blocks, the physical cache rows are inside the view, and the query tokens of the requests are
consecutive and inside the token count.
-/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX TensorDescriptor

/-- The tensor map of the cache view is valid. -/
theorem mapKv_valid {P : Params}
    (kvAlign : P.kvBase % 16 = 0) (slotStridePos : 0 < P.slotStride)
    (slotStrideAlign : P.slotStride % 8 = 0) (slotStrideRange : P.slotStride ≤ 2 ^ 31)
    (rowsPos : 0 < P.rows) (rowsRange : P.rows ≤ 2 ^ 31) :
    TensorDescriptor.Valid (mapKv P.kvBase P.slotStride P.rows P.kvClass) := by
  have hsw : TensorTile.swizzleWidth .b128 = 128 := by decide
  unfold TensorDescriptor.Valid mapKv
  refine ⟨by decide, kvAlign, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> omega
  · intro i
    fin_cases i
    simp
    omega
  · intro i
    fin_cases i <;> simp
  · intro i
    fin_cases i <;> simp
  · simp [Format.bytes]
  · right
    simp [Format.bytes, hsw]
  · intro h
    simp at h
  · simp

/-- A request has at most `nBias r + 10` key blocks, so at most `REL_PAD = 1280` keys lie in the
blocks with relative logits. -/
theorem blocks_le_nBias {P : Params} {r : Nat} (hLe : P.qLen r ≤ 10)
    (hSeq : P.qLen r ≤ P.seqK r) : P.blocks r ≤ P.nBias r + 10 := by
  unfold Params.blocks Params.nBias Params.past
  omega

/-- The relative-logit column of a key in a block with relative logits is inside the row. -/
theorem relCol_range {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {r k : Nat} (hr : r < P.b) (hk : k < P.blocks r * 128) (hb : P.nBias r * 128 ≤ k) :
    0 ≤ relCol P r k ∧ relCol P r k < relPad := by
  have h := blocks_le_nBias (hpre.qLenLe r hr) (hpre.qLenSeq r hr)
  unfold relCol relPad
  omega

/-- Split `s` processes the blocks `s + i * splits` for `i < numIters`. -/
theorem numIters_spec {P : Params} {r s k : Nat} (hsp : 0 < P.splits) :
    P.inSplit r s k ↔ s ≤ k / 128 ∧ ∃ i < P.numIters r s, k / 128 = s + i * P.splits := by
  unfold Params.inSplit Params.numIters
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hi : (k / 128 - s) / P.splits * P.splits = k / 128 - s :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)
    refine ⟨h1, (k / 128 - s) / P.splits, ?_, by omega⟩
    refine Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hsp).2 ?_)
    rw [Nat.succ_mul]
    omega
  · rintro ⟨h1, i, hi, he⟩
    have h := (Nat.le_div_iff_mul_le hsp).1 (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at h
    refine ⟨h1, ?_, by omega⟩
    rw [he, Nat.add_sub_cancel_left]
    exact Nat.mul_mod_left _ _

/-- The tokens of request `r` end where those of request `r + 1` begin. -/
theorem qStart_le {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {r : Nat} (hr : r < P.b) : P.qStart r + P.qLen r ≤ P.qStart (r + 1) := by
  have := hpre.cuMono r hr
  unfold Params.qLen
  omega

/-- The first token of a request is monotone in the request. -/
theorem qStart_mono {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {r r' : Nat} (h : r ≤ r') (hr' : r' ≤ P.b) : P.qStart r ≤ P.qStart r' := by
  induction r', h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n hn ih =>
    exact Nat.le_trans (ih (by omega)) (hpre.cuMono n (by omega))

/-- The tokens of every request are inside the token count. -/
theorem token_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {r tok : Nat} (hr : r < P.b) (htok : tok < P.qLen r) : P.qStart r + tok < P.nTok := by
  have h1 := qStart_le hpre hr
  have h2 := qStart_mono hpre (r := r + 1) (r' := P.b) (by omega) (Nat.le_refl _)
  have h3 := hpre.cuEnd
  omega

end PTX.Kernels.InklingRelDecode.Proof
