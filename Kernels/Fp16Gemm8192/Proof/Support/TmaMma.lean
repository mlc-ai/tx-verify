-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.Ring
public import Kernels.Fp16Gemm8192.Data.TensorMaps
public import Lemmas.Tensor.TensorMemory
public import Lemmas.Tcgen05.TcSharedAddress

@[expose] public section

/-! TMA → MMA hand-off of the production FP16 GEMM's operand tiles.

A TMA load with map `A` (or `B`) writes a 64 x 128 box of FP16 elements into a
128-byte-swizzled shared stage. The MMA consumes the stage in four K steps of 16 elements,
each with a K-major, 128-byte-swizzled shared descriptor whose start advances 32 bytes per
step. For every element and byte of the box, the shared byte the TMA writes is the byte
that K step's MMA descriptor addresses. This is the address half of the producer/consumer
hand-off; the ordering half is the pipeline's mbarrier protocol. -/
namespace PTX.Kernels.Fp16Gemm8192
open TensorDescriptor

/-- The MMA shared descriptor for K step `t` of a stage at `stage`. -/
def stepDescriptor (stage leading t : Nat) : TcShared.Descriptor :=
  ⟨stage + 2 * (16 * t), leading, 1024, 0, false, false, .b128⟩

/-- A TMA load of operand map `d` into a stage at shared address `stage` of CTA `cta`. -/
def stageCopy (d : Descriptor 1) (origin : Fin 2 → Int) (cta stage : Nat) (mbar : Loc)
    (clusterAddress : Bool) (group : CtaGroup) : TensorCopy.Spec :=
  ⟨⟨1, d, origin, ⟨.shared, cta, stage⟩, none⟩, mbar, clusterAddress, group⟩

/-- Where a 64 x 128 FP16, 128-byte-swizzled box writes element `(x, y)`, byte `byte`. -/
theorem box_writeLoc {base stage cta x y byte : Nat} {cls : AllocationClass}
    {origin : Fin 2 → Int} {mbar : Loc} {ca : Bool} {grp : CtaGroup}
    (hx : x < 64) (hy : y < 128) (hb : byte < 2) :
    TensorCopy.writeLoc (stageCopy (mapA base cls) origin cta stage mbar ca grp) x y byte =
      some ⟨.shared, cta, stage +
        TensorSwizzle.offset .b128 stage (128 * y + 2 * x + byte)⟩ := by
  have c0 : TensorTile.count (mapA base cls).box 0 = 64 := by
    simp [mapA, encodeTiled, TensorTile.count, TensorTile.step]
  have c1 : TensorTile.count (mapA base cls).box 1 = 128 := by
    simp [mapA, encodeTiled, TensorTile.count, TensorTile.step]
  unfold TensorCopy.writeLoc TensorTransfer.slotAt
  rw [dite_eq_left (show x < TensorTile.count
      (stageCopy (mapA base cls) origin cta stage mbar ca grp).descriptor.box 0 from
      (show x < TensorTile.count (mapA base cls).box 0 by omega)),
    dite_eq_left (show y < TensorTile.rows
      (stageCopy (mapA base cls) origin cta stage mbar ca grp).descriptor.box from
      (show y < TensorTile.count (mapA base cls).box 1 by omega)),
    dite_eq_left (show byte <
      (stageCopy (mapA base cls) origin cta stage mbar ca grp).descriptor.format.bytes from hb)]
  rw [Option.map_some]
  simp only [stageCopy]
  simp [TensorBox.sharedLoc,
    TensorTile.sharedByte, TensorTile.linearByte, TensorTile.rowBytes, mapA, encodeTiled,
    TensorTile.swizzleWidth, Format.bytes]
  have hc : TensorTile.count
      ({ size := fun i => if i = 0 then 64 else 128, traversal := fun _ => 1 } : TensorTile.Box 2)
      0 = 64 := by simp [TensorTile.count, TensorTile.step]
  rw [hc]
  congr 1
  simp only [max_self]
  ring

/-- **TMA → MMA addresses.** For every K step `t < 4`, row `y < 128`, contraction index
`k < 16` and byte of an `A` stage (any 128-byte-aligned stage address), the TMA write of
element `(16 t + k, y)` and the MMA operand read of row `y`, contraction `k` under step
`t`'s descriptor are the same shared byte. -/
theorem tma_mma_same_byte {base stage cta t y k byte leading : Nat} {cls : AllocationClass}
    {origin : Fin 2 → Int} {mbar : Loc} {ca : Bool} {grp : CtaGroup}
    (hs : stage % 128 = 0) (ht : t < 4) (hy : y < 128) (hk : k < 16) (hb : byte < 2) :
    (TensorCopy.writeLoc (stageCopy (mapA base cls) origin cta stage mbar ca grp)
        (16 * t + k) y byte).map Loc.addr =
      TcShared.byteAddress 2 .k (stepDescriptor stage leading t) y k byte := by
  rw [box_writeLoc (by omega) hy hb, stepDescriptor,
    TcShared.k128_tma_byte 2 stage (16 * t) leading y k byte hs hb]
  rfl

/-- The production PTX builds its operand descriptors as `4611756662049472512 + s` for a
stage at shared address `16 s` and adds `2 t` for K step `t` (`add.s64 %rd43, %rd41, 2`,
`... 4`, `... 6`): exactly `stepDescriptor (16 s) 0 t`. -/
theorem production_descriptor {s t x : Nat} (hs : s + 2 * t < 32768)
    (hx : 4611756662049472512 + s + 2 * t = x) :
    TcShared.decode x = some (stepDescriptor (16 * s) 0 t) := by
  have h0 : x / 2305843009213693952 % 8 = 2 := by omega
  have h1 : x < 18446744073709551616 := by omega
  have h2 : x / 32768 % 2 = 0 := by omega
  have h3 : x / 2147483648 % 2 = 0 := by omega
  have h4 : x / 70368744177664 % 8 = 1 := by omega
  have h5 : x / 18014398509481984 % 128 = 0 := by omega
  have h6 : x % 32768 = s + 2 * t := by omega
  have h7 : x / 65536 % 32768 = 0 := by omega
  have h8 : x / 4294967296 % 16384 = 64 := by omega
  have h9 : x / 562949953421312 % 8 = 0 := by omega
  have h10 : x / 4503599627370496 % 2 = 0 := by omega
  have h11 : x / 9007199254740992 % 2 = 0 := by omega
  simp only [TcShared.decode, Nat.reducePow, h0, TcShared.decodeSwizzle, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, h11, and_self, ↓reduceIte, Nat.reduceMul]
  simp only [stepDescriptor, Option.some.injEq, TcShared.Descriptor.mk.injEq]
  exact ⟨by ring, trivial, trivial, trivial, rfl, rfl, trivial⟩

/-- **Production hand-off.** The operand descriptor the production PTX passes for K step
`t < 4` of an `A` stage at `16 s` (a 128-byte-aligned address) addresses, for every row,
contraction index and byte, exactly the shared byte the stage's TMA load wrote. -/
theorem production_mma_reads_tma {base s t y k byte : Nat} {cls : AllocationClass}
    {origin : Fin 2 → Int} {cta : Nat} {mbar : Loc} {ca : Bool} {grp : CtaGroup}
    (hal : (16 * s) % 128 = 0) (hs : s + 2 * t < 32768) (ht : t < 4) (hy : y < 128)
    (hk : k < 16) (hb : byte < 2) :
    (TensorCopy.writeLoc (stageCopy (mapA base cls) origin cta (16 * s) mbar ca grp)
        (16 * t + k) y byte).map Loc.addr =
      (TcShared.decode (4611756662049472512 + s + 2 * t)).bind
        fun d => TcShared.byteAddress 2 .k d y k byte := by
  rw [production_descriptor hs rfl, Option.bind_some]
  exact tma_mma_same_byte hal ht hy hk hb

end PTX.Kernels.Fp16Gemm8192
