-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftKernel
public import Kernels.InklingRelDecode.Proof.Lib.SoftWords

@[expose] public section

/-! # The epilogue's words as functions of the row's state

The epilogue stores `o * rcp l` for the accumulator word `o` (the operand of `rcp` is `1.0` when
`l = 0`) and `scale * log2e * m + log2 l` (the `-inf` pattern when `l = 0`). With the kernel's
state `kState` (sum `l`, maximum `m`) and the accumulator word of `rowState` these are the
specification's words. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof Lib.SoftRow Lib.SoftFold

noncomputable section

/-- The word the epilogue stores for an accumulator word `o` and the row sum `l`. -/
def epiOutWord (o l : ℝ) : Value := .float .f32 (o * (1 / if l = 0 then 1 else l))

/-- The log2 normalizer the epilogue stores for the carried maximum `m` and sum `l`. -/
def epiLseWord (sc : ℝ) (m : EReal) (l : ℝ) : Value :=
  if l = 0 then (FVal.inf true).toValue .f32 else .float .f32 (sc * m.toReal + Real.logb 2 l)

theorem epiOut_eq (P : Params) (hsp : 0 < P.splits) (hs : 0 < P.scale) (r s tok h d : Nat) :
    epiOutWord (rowState P r s tok h d).o (kState P r s tok h d).l =
      .float .f32 (oPart P r s tok h d) := by
  have key := oPart_kernel P hsp hs r s tok h d
  have ho : (rowState P r s tok h d).o = (kState P r s tok h d).o := by rw [rowState_eq P hs]; rfl
  unfold epiOutWord
  by_cases hl : (kState P r s tok h d).l = 0
  · have hz : rowSum P r s tok h = 0 := (rowSum_kernel P hsp hs r s tok h d).2 hl
    have hrs : (rowState P r s tok h d).l = 0 := (rowSum_zero_iff P hsp r s tok h d).1 hz
    have hflat : (rowBlocks P r s tok h d).flatten = [] := by
      by_contra e
      exact (fold_normalized _ log2e_pos _ e).2.ne' hrs
    have h0 := (fold_empty _ log2e_pos _ hflat).2.1
    have : (rowState P r s tok h d).o = 0 := h0
    simp [hl, this, oPart, hz]
  · simp only [hl, ↓reduceIte, ho, key]
    congr 1
    field_simp

theorem epiLse_eq (P : Params) (hsp : 0 < P.splits) (hs : 0 < P.scale) (r s tok h d : Nat) :
    epiLseWord (P.scale * log2eF32) (kState P r s tok h d).m (kState P r s tok h d).l =
      if rowSum P r s tok h = 0 then (FVal.inf true).toValue .f32
      else .float .f32 (lsePart P r s tok h) := by
  by_cases hz : rowSum P r s tok h = 0
  · simp [epiLseWord, hz, (rowSum_kernel P hsp hs r s tok h d).1 hz]
  · have hl : (kState P r s tok h d).l ≠ 0 := fun e => hz ((rowSum_kernel P hsp hs r s tok h d).2 e)
    simp only [epiLseWord, hl, hz, ↓reduceIte, lsePart_kernel P hsp hs d hz]
    congr 2
    ring

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
