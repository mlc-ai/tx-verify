-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmReuseEndpoints
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # The query copies cover the first byte written by each dequantizer lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GemmReuseEndpoints

open PTX PTX.Flow

/-- Undo the shared swizzle and partition the whole Q window among the sixteen copy issues. -/
theorem query_covers_window_byte {P : Params} {L : Launch} {mem0 : Mem0} {g addr : Nat}
    (hpre : Pre P L mem0) (hlo : L.sharedBase ≤ addr) (hhi : addr < L.sharedBase + 65536) :
    ∃ (issue : Fin 16) (index : Nat),
      let sp := MmaDataTrace.queryCopySpec L g issue
      index < sp.shape.sourceBytes ∧
      TcCopy.byteLoc sp.shape sp.src (ctaOf L g) index = some ⟨.shared, ctaOf L g, addr⟩ := by
  let linear := TensorSwizzle.offset .b128 0 addr
  have hrow : linear / 128 = addr / 128 := TensorSwizzle.offset_row .b128 0 addr
  have hbase : L.sharedBase % 1024 = 0 := hpre.sharedBase ▸ hpre.sharedAlignment
  have hLinearLo : L.sharedBase ≤ linear := by omega
  let n := linear - L.sharedBase
  have hWindow : n < 65536 := by dsimp only [n]; omega
  let row : Fin 128 := ⟨n % 8192 / 128 + 64 * (n / 8192 % 2), by omega⟩
  let issue : Fin 16 := ⟨4 * (n / 8192 / 2) + n % 128 / 32, by omega⟩
  let k : Fin 16 := ⟨n % 32 / 2, by omega⟩
  let b : Fin 2 := ⟨n % 2, by omega⟩
  let index := 2 * (row.val * 16 + k.val) + b.val
  refine ⟨issue, index, ?_, ?_⟩
  · change index < 4096
    dsimp only [index, row, k, b]
    omega
  have hFeature : MmaDataTrace.qkFeature issue row k =
      64 * (n / 8192) + n % 128 / 2 := by
    simp only [MmaDataTrace.qkFeature, issue, row, k]
    omega
  have hAddr : MmaDataTrace.kvLinearByte L 0 (row.val % 64)
      (MmaDataTrace.qkFeature issue row k) b.val = linear := by
    rw [hFeature]
    simp only [MmaDataTrace.kvLinearByte, Wg1Mma.kvBase, row, b,
      Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
    dsimp only [n]
    omega
  rw [MmaDataTrace.queryCopyByteLoc L g issue row k b, hAddr]
  change some (Loc.mk .shared (ctaOf L g) (TensorSwizzle.offset .b128 0 linear)) = _
  rw [show TensorSwizzle.offset .b128 0 linear = addr from
    TensorSwizzle.offset_involutive .b128 0 addr]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GemmReuseEndpoints
