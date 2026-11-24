-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Tensor maps of the FlashAttention-4 forward kernel, as functions of the shape.

The PTX receives each map as an opaque 128-byte `.param` (`param_4` .. `param_7` for Q, K, V,
O). The host builds them with CuTeDSL's `make_tiled_tma_atom` (closed source) over the tensors
`flash_attn_func` passes: contiguous `(batch, seqlen, heads, 128)` f16 tensors
(`interface.py`: inputs with unit last stride, output from `torch.empty`), viewed by
`flash_fwd_sm100.py` with the head dimension first. Each map is rank 4 with dimension order
(head dimension, row, head, batch), the order of the coordinates `{d, row, head, batch}` of
every `cp.async.bulk.tensor.4d` in the PTX; for V the CuTe view is transposed
(`V_layout_transpose`) but its TMA dimension 0 is still the contiguous head dimension (the V
loads' coordinate 0 is `64 * rank`).

* Extents: 128 head-dimension elements, `rows` (`seqlen_q` for Q and O, `seqlen_k` for K and
  V), `heads`, `batch`.
* Strides (bytes, dimensions 1..3): row `256 * heads`, head `256`, batch
  `256 * heads * rows` (contiguous `(batch, rows, heads, 128)` f16).
* Boxes: 64 head-dimension elements (128 bytes, the 128-byte swizzle span) by 128 rows for
  Q, V and O and by 64 rows for K, one head, one batch; unit traversal strides. Derived from
  the PTX: the loads and stores address head-dimension coordinates 0 and 64 only; the shared
  destinations of one copy are 16384 bytes apart for Q, O and V (8192 for K, whose second box
  of the slot is at `+8192` and whose row coordinate is `128 * block + 64 * rank`); and the
  expected transaction bytes are 65536 per Q stage of the CTA pair (2 CTAs x 2 boxes x 16384)
  and 32768 per K or V slot (K: 2 CTAs x 2 boxes x 8192; V: 2 CTAs x 1 box x 16384).
* Swizzle: 128 bytes. The shared layouts are CuTe's 128-byte-swizzle atoms (64 f16 per row),
  and the correction warps write the O staging rows with the 128-byte XOR pattern
  (`A ^ ((A >> 3) & 0x70)`).
* Element type f16; non-interleaved (Core represents only that layout).

Not determinable from the available material (the encoding is compiled into CuTeDSL's MLIR
lowering): the out-of-bounds fill mode, the L2 promotion and the allocation class. The fill and
the allocation class stay parameters (the kernel's coordinates stay in bounds in scope, so
neither is observed); L2 promotion is a cache hint with no memory-model effect and is not
represented. -/
namespace PTX.Kernels.FlashAttn4Fwd
open TensorDescriptor

/-- A rank-4 f16 tensor map over a contiguous `(batch, rows, heads, 128)` tensor, with the head
dimension first: box `64 x boxRows x 1 x 1`, 128-byte swizzle. -/
def encodeTiled (base rows heads batch boxRows : Nat) (fill : Fill) (cls : AllocationClass) :
    Descriptor 3 where
  format := .f16
  base := base
  extent := ![128, rows, heads, batch]
  outerStride := ![256 * heads, 256, 256 * heads * rows]
  box := ⟨![64, boxRows, 1, 1], fun _ => 1⟩
  swizzle := .b128
  fill := fill
  allocationClass := cls

/-- Q: `seqlen_q` rows, boxes of 128 rows. -/
def mapQ (base sq h b : Nat) (fill : Fill) (cls : AllocationClass) : Descriptor 3 :=
  encodeTiled base sq h b 128 fill cls
/-- K: `seqlen_k` rows, boxes of 64 rows (each CTA of the pair loads half of a 128-row block). -/
def mapK (base sk h b : Nat) (fill : Fill) (cls : AllocationClass) : Descriptor 3 :=
  encodeTiled base sk h b 64 fill cls
/-- V: `seqlen_k` rows, boxes of 128 rows (each CTA of the pair loads 64 head-dimension
columns). -/
def mapV (base sk h b : Nat) (fill : Fill) (cls : AllocationClass) : Descriptor 3 :=
  encodeTiled base sk h b 128 fill cls
/-- O: `seqlen_q` rows, boxes of 128 rows (the epilogue's TMA stores). -/
def mapO (base sq h b : Nat) (fill : Fill) (cls : AllocationClass) : Descriptor 3 :=
  encodeTiled base sq h b 128 fill cls

theorem encodeTiled_valid {base rows heads batch boxRows : Nat} {fill : Fill}
    {cls : AllocationClass} (hBase : base % 16 = 0) (hRows : 0 < rows ∧ rows ≤ 2 ^ 32)
    (hHeads : 0 < heads) (hBatch : 0 < batch ∧ batch ≤ 2 ^ 32)
    (hStride : 256 * heads * rows < 2 ^ 40) (hBox : 0 < boxRows ∧ boxRows ≤ 256) :
    Valid (encodeTiled base rows heads batch boxRows fill cls) := by
  have hh : 256 * heads ≤ 256 * heads * rows := Nat.le_mul_of_pos_right _ hRows.1
  have hm : 256 * heads * rows = 16 * (16 * heads * rows) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc]
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [encodeTiled, Format.bytes],
    .inr (by simp [encodeTiled, Format.bytes, TensorTile.swizzleWidth]), fun _ => rfl, rfl⟩
  · fin_cases i <;> simp [encodeTiled] <;> omega
  · fin_cases i <;> simp [encodeTiled] <;> omega
  · fin_cases i <;> simp [encodeTiled]; exact hBox
  · simp [encodeTiled]

end PTX.Kernels.FlashAttn4Fwd
