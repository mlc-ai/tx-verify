-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftRow
public import Kernels.InklingRelDecode.Proof.Lib.SoftScale

@[expose] public section

/-!
# The row's state in the kernel's domain

`kBlocks` are the row's blocks with the scores divided by `scale` (the kernel's `S + bias / scale`);
`rowState` is the scaled `SoftFold.run` of them with the constant `scale * log2e`, so `l` and `o`
are the kernel's and the maximum is `scale` times the kernel's.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow

open SoftFold

/-- The row's blocks in the kernel's domain. -/
noncomputable def kBlocks (P : Params) (r s tok h d : Nat) : List (List (ℝ × ℝ)) :=
  (rowBlocks P r s tok h d).map fun blk => blk.map fun q => (q.1 / P.scale, q.2)

/-- The kernel's final state of a row, in its own domain. -/
noncomputable def kState (P : Params) (r s tok h d : Nat) : St :=
  run (P.scale * log2eF32) (kBlocks P r s tok h d)

theorem rowState_eq (P : Params) {r s tok h d : Nat} (hs : 0 < P.scale) :
    rowState P r s tok h d = scaleSt P.scale (kState P r s tok h d) := by
  have hl : 0 < log2eF32 := by norm_num [log2eF32]
  unfold rowState kState kBlocks
  rw [← run_scale hs hl, List.map_map]
  congr 1
  conv_lhs => rw [← List.map_id (rowBlocks P r s tok h d)]
  refine List.map_congr_left fun blk _ => ?_
  simp only [scaleBlk, Function.comp, List.map_map, id]
  refine ((List.map_congr_left fun q _ => ?_).trans (List.map_id' blk)).symm
  simp [mul_div_cancel₀ _ hs.ne']

theorem oPart_kernel (P : Params) (hsp : 0 < P.splits) (hs : 0 < P.scale) (r s tok h d : Nat) :
    oPart P r s tok h d = (kState P r s tok h d).o / (kState P r s tok h d).l := by
  rw [oPart_eq P hsp, rowState_eq P hs]
  rfl

theorem rowSum_kernel (P : Params) (hsp : 0 < P.splits) (hs : 0 < P.scale) (r s tok h d : Nat) :
    rowSum P r s tok h = 0 ↔ (kState P r s tok h d).l = 0 := by
  rw [rowSum_zero_iff P hsp r s tok h d, rowState_eq P hs]
  rfl

theorem lsePart_kernel (P : Params) (hsp : 0 < P.splits) (hs : 0 < P.scale) {r s tok h : Nat}
    (d : Nat) (nz : rowSum P r s tok h ≠ 0) :
    lsePart P r s tok h = (kState P r s tok h d).m.toReal * (P.scale * log2eF32) +
      Real.logb 2 (kState P r s tok h d).l := by
  rw [lsePart_eq P hsp r s tok h d nz, rowState_eq P hs]
  simp only [scaleSt, toReal_cmul hs]
  ring

end PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow
