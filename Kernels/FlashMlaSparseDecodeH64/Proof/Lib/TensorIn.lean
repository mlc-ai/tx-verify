-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Core.Async.Tensor.TensorStoreMemory
public import Core.Async.Tensor.TensorMemory
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # The in-bounds global bytes of the kernel's tensor maps

A tensor load reads, and a tensor store writes, a global byte only for an element inside the
tensor (`readLoc_lookup`, `writeLoc_lookup`: the byte is an address the geometry's `lookup`
returns). For the kernel's maps these addresses are the input formulas of `Pre`: a byte of the
`(b, s_q, 64, 512)` bf16 view (`tiled_in`, Q and O) or of a 528-byte row of a cache (`kv_in`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

/-- **A cache map**: the main cache's map, or the extra cache's when it is on. -/
def KvMap (P : Params) (y : Σ n, Descriptor n) : Prop :=
  y = ⟨1, mapKv P.kvBase P.numBlocks P.blockStride P.kvClass⟩ ∨
    (P.extra_topk ≠ 0 ∧
      y = ⟨1, mapExtraKv P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass⟩)

/-- A tensor load's global byte is an in-bounds address of its descriptor's geometry. -/
theorem readLoc_lookup {s : TensorCopy.Spec} {x y k : Nat} {l : Loc}
    (h : TensorCopy.readLoc s x y k = some l) :
    ∃ coord byte addr, TensorAddress.lookup (geometry s.descriptor) coord byte = some addr ∧
      l = ⟨.global, 0, addr⟩ := by
  simp only [TensorCopy.readLoc, TensorTransfer.sourceLoc, TensorTransfer.globalAddress,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨slot, -, addr, ha, rfl⟩ := h
  exact ⟨_, _, addr, ha, rfl⟩

/-- A tensor store's global byte is an in-bounds address of its descriptor's geometry. -/
theorem writeLoc_lookup {s : TensorStore.Spec} {x y k : Nat} {l : Loc}
    (h : TensorStore.writeLoc s x y k = some l) :
    ∃ coord byte addr, TensorAddress.lookup (geometry s.descriptor) coord byte = some addr ∧
      l = ⟨.global, 0, addr⟩ := by
  simp only [TensorStore.writeLoc, TensorStore.destination,
    TensorBox.globalAddress, TensorTransfer.globalAddress, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at h
  obtain ⟨slot, -, addr, ha, rfl⟩ := h
  exact ⟨_, _, addr, ha, rfl⟩

/-- **The coordinates of an in-bounds byte of a tiled map** (Q, O): byte `y < 2` of element
`(e, q, h, t)` of the `(b, s_q, 64, 512)` view at `base`, whose coordinates are `(t, h, q, e)`. -/
theorem tiled_coord {o : Nat} {d : Descriptor o} {base sq b : Nat} {fill : Fill}
    {cls : AllocationClass}
    (hd : (⟨o, d⟩ : Σ n, Descriptor n) =
      ⟨3, encodeTiled base 512 32768 (sq * 32768) sq b fill cls⟩)
    {coord : Fin (o + 1) → Int} {byte addr : Nat}
    (h : TensorAddress.lookup (geometry d) coord byte = some addr) :
    ∃ e : Nat, e < b ∧ ∃ q : Nat, q < sq ∧ ∃ hh : Nat, hh < 64 ∧ ∃ t : Nat, t < 512 ∧
      ∃ y : Nat, y < 2 ∧ coord 0 = t ∧ coord 1 = hh ∧ coord 2 = q ∧ coord 3 = e ∧ byte = y ∧
      addr = base + 2 * (((e * sq + q) * 64 + hh) * 512 + t) + y := by
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hd
  cases hd
  unfold TensorAddress.lookup at h
  split_ifs at h with hb
  obtain ⟨hc, hy⟩ := hb
  cases h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  simp only [geometry, encodeTiled, Format.bytes, Matrix.cons_val, Fin.isValue] at h0 h1 h2 h3 hy
  refine ⟨(coord 3).toNat, by omega, (coord 2).toNat, by omega, (coord 1).toNat, by omega,
    (coord 0).toNat, by omega, byte, hy, by omega, by omega, by omega, by omega, rfl, ?_⟩
  simp [TensorAddress.byteAddress, Fin.sum_univ_succ, geometry, encodeTiled, Format.bytes]
  ring

/-- **An in-bounds byte of a tiled map** (Q, O) is byte `y < 2` of element `(e, q, h, t)` of the
`(b, s_q, 64, 512)` view at `base`. -/
theorem tiled_in {o : Nat} {d : Descriptor o} {base sq b : Nat} {fill : Fill}
    {cls : AllocationClass}
    (hd : (⟨o, d⟩ : Σ n, Descriptor n) =
      ⟨3, encodeTiled base 512 32768 (sq * 32768) sq b fill cls⟩)
    {coord : Fin (o + 1) → Int} {byte addr : Nat}
    (h : TensorAddress.lookup (geometry d) coord byte = some addr) :
    ∃ e < b, ∃ q < sq, ∃ hh < 64, ∃ t < 512, ∃ y < 2,
      addr = base + 2 * (((e * sq + q) * 64 + hh) * 512 + t) + y := by
  obtain ⟨e, he, q, hq, hh, hhh, t, ht, y, hy, -, -, -, -, -, ha⟩ := tiled_coord hd h
  exact ⟨e, he, q, hq, hh, hhh, t, ht, y, hy, ha⟩

/-- **An in-bounds byte of a cache map** is byte `y < 528` of row `r` of the cache at `base`. -/
theorem kv_in {o : Nat} {d : Descriptor o} {base nb bs : Nat} {cls : AllocationClass}
    (hd : (⟨o, d⟩ : Σ n, Descriptor n) = ⟨1, encodeKv base nb bs cls⟩)
    {coord : Fin (o + 1) → Int} {byte addr : Nat}
    (h : TensorAddress.lookup (geometry d) coord byte = some addr) :
    ∃ r < nb * (bs / 528), ∃ y < 528, addr = base + r * 528 + y := by
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hd
  cases hd
  unfold TensorAddress.lookup at h
  split_ifs at h with hb
  obtain ⟨hc, hy⟩ := hb
  cases h
  have h0 := hc 0
  have h1 := hc 1
  simp only [geometry, encodeKv, Format.bytes, Matrix.cons_val, Fin.isValue] at h0 h1 hy
  refine ⟨(coord 1).toNat, by omega, 4 * (coord 0).toNat + byte, by omega, ?_⟩
  simp [TensorAddress.byteAddress, Fin.sum_univ_succ, geometry, encodeKv, Format.bytes]
  ring

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
