-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.All
public import Kernels.InklingRelDecode.Proof.Result.MmaLayout
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox
public import Lemmas.Tensor.TensorReadSources
public import Lemmas.Tensor.TensorAddress

@[expose] public section

/-!
# What a K/V tensor copy writes

A copy of the kernel's `kv_rows` map (`kvCopySpec Q cta col row dst bar`: the `(64, 64)` bf16 box
at origin `(col, row)`, 128-byte swizzle) copies the bf16 elements of the cache:

* `kv_readLoc`: the box element `(x, y)`, byte `z`, of a box inside the map is read from the global
  byte `kvBase + 2 (slotStride · r + c) + z` of the element `(r, c) = (row + y, col + x)`
  (the port of Fp16Gemm8192's `copy_readLoc` to `mapKv`, listed for promotion);
* `kv_noOob`: a box `[col, col + 64) × [row, row + 64)` inside `[0, slotStride) × [0, rows)` has
  no out-of-bounds element;
* `kv_copy_written`: for the box of a block-table slab `s` of request `r`, KV head `kvh`, K or V
  (`isV`), half `hh`, origin `(kvh · head_cols + 128 isV + 64 hh, page r s · page_rows + kvh ·
  head_rows)` (the quantities `EvW.ldCopy_origin` gives the loader's copies), the byte the copy
  writes at slot `(x, y, z)` is byte `z` of the bf16 element
  `kv (page r s · page_rows + kvh · head_rows + y) (kvh · head_cols + 128 isV + 64 hh + x)`:
  the cache's value at that row and column. No write reaches an input byte (a global write is an
  epilogue store into `OPart`/`LsePart`, `ThreadFacts.write_in_arrays`, apart from every byte the
  kernel reads, `Pre.outputsApart`), so the copy reads the launch byte (`Pre.kvInput`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof TensorDescriptor
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec i32)
open PTX.Kernels.InklingRelDecode.Proof.Interface (ThreadFacts)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A K/V copy writes the cache's bf16 element.** The byte the copy of the box at origin
`(kvh · head_cols + 128 isV + 64 hh, page r s · page_rows + kvh · head_rows)` writes at slot
`(x, y, z)` is byte `z` of the cache element at the origin plus `(x, y)`. -/
theorem kv_copy_written (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) {c : EvId} {o : TensorCopy.Observation}
    {cta dst : Nat} {bar : Loc} {r s kvh isV hh : Nat} (hr : r < Q.b)
    (hs : s < 2 * Q.blocks r) (hkvh : kvh < 2) (hV : isV ≤ 1) (hH : hh ≤ 1)
    (hobs : X.tensor c = some o)
    (hspec : o.spec = kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar)
    {x y z : Nat} (hx : x < 64) (hy : y < 64) (hz : z < 2) {b : Byte}
    (hw : TensorCopy.writeByte o x y z = some b) :
    b = (Value.float .bf16 (Q.kv (Q.page r s * Q.pageRows + kvh * Q.headRows + y)
      (kvh * Q.headCols + 128 * isV + 64 * hh + x))).byteAt z := by
  obtain ⟨addr, hTI⟩ := (hX.tensor c o hobs).1
  have hkc := hpre.kvCols kvh (by unfold kvHeads; omega)
  have hsl := hpre.slotStrideRange
  have hrr := hpre.rowsRange
  have hslab := hpre.slabInside r hr s hs kvh (by unfold kvHeads; omega)
  unfold headDim at hkc
  have hno := kv_noOob Q (col := kvh * Q.headCols + 128 * isV + 64 * hh)
    (row := Q.page r s * Q.pageRows + kvh * Q.headRows) (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨rr, cc, hrr', hcc', hl⟩ := kv_readLoc Q cta _ _ dst bar (x := x) (y := y) (z := z)
    hno hx hy hz
  rw [← hspec] at hl
  rw [EvW.i32_of_lt (by omega)] at hrr' hcc'
  have hr2 : rr = Q.page r s * Q.pageRows + kvh * Q.headRows + y := by omega
  have hc2 : cc = kvh * Q.headCols + 128 * isV + 64 * hh + x := by omega
  subst hr2 hc2
  have hm := hpre.kvInput r hr s hs kvh (by unfold kvHeads; omega) y hy
    (128 * isV + 64 * hh + x) (by unfold headDim; omega) z hz
  have hloc : (⟨.global, 0, Q.kvBase + 2 * (Q.slotStride * (Q.page r s * Q.pageRows +
      kvh * Q.headRows + y) + (kvh * Q.headCols + 128 * isV + 64 * hh + x)) + z⟩ : Loc) =
      ⟨.global, 0, Q.kvBase + 2 * ((Q.page r s * Q.pageRows + kvh * Q.headRows + y) *
        Q.slotStride + kvh * Q.headCols + (128 * isV + 64 * hh + x)) + z⟩ := by
    congr 1
    ring
  rw [hloc] at hl
  refine tensor_writeByte_of_initial hX hobs hTI hl hw (hm.trans ?_) ?_
  · have : kvh * Q.headCols + (128 * isV + 64 * hh + x) =
        kvh * Q.headCols + 128 * isV + 64 * hh + x := by omega
    rw [this]
  · intro w a bs hwr hcov
    have hsp : a.loc.space = .global := hcov.1.symm.trans rfl
    have hap := hpre.outputsApart _ (Or.inr (Or.inr (Or.inl ⟨r, hr, s, hs, kvh,
      by unfold kvHeads; omega, y, hy, 128 * isV + 64 * hh + x, by unfold headDim; omega, z, hz,
      rfl⟩)))
    rcases hf.write_in_arrays hwr hsp hcov with h | h
    · exact hap.1 h
    · exact hap.2 h

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
