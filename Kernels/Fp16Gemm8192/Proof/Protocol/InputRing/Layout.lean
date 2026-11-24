-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Stage
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # Which input-stage bytes the loads write and the MMAs read

A load of a tile writes element `(x, y)` byte `byte` of the box at `stageByte` of its CTA and
stage (`copy_writeLoc`). The MMA of K step `j` reads, for row `128 r + y` of its operand, the
byte `stageByte` of element `(16 j + k, y)` of the tile in CTA `r` of the pair (`mma_byteLoc`),
and every element of the tile is so read (`mma_byteLoc_cover`). Distinct tiles and distinct
elements of a tile are distinct bytes (`stageByte_inj`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.InputRing
open PTX TensorDescriptor

/-- The tile an operand of MMA warp `8 + w % 2` reads: its own A tile or the B tile. -/
def opTile (w : Nat) : TcMma.Operand → Nat
  | .a => w % 2
  | .b => 2

theorem mmaDescriptor_valid : TcMma.Valid mmaDescriptor := by decide

/-- A load's write location: an element of the 64 x 128 box, at its swizzled stage byte. -/
theorem copy_writeLoc {base stage cta x y byte : Nat} {cls : AllocationClass}
    {origin : Fin 2 → Int} {mbar : Loc} {ca : Bool} {grp : CtaGroup} {l : Loc}
    (h : TensorCopy.writeLoc (stageCopy (mapA base cls) origin cta stage mbar ca grp) x y byte =
      some l) :
    x < 64 ∧ y < 128 ∧ byte < 2 ∧ l = stageByte cta stage x y byte := by
  have hb3 : x < 64 ∧ y < 128 ∧ byte < 2 := by
    unfold TensorCopy.writeLoc TensorTransfer.slotAt at h
    split at h
    · rename_i hx
      split at h
      · rename_i hy
        split at h
        · rename_i hb
          simp only [stageCopy, mapA, encodeTiled, TensorTile.count, TensorTile.step,
            TensorTile.rows, TensorTile.rowsOf, TensorDescriptor.Format.bytes] at hx hy hb
          exact ⟨by simpa using hx, by simpa using hy, by simpa using hb⟩
        · simp at h
      · simp at h
    · simp at h
  obtain ⟨hx, hy, hb⟩ := hb3
  rw [box_writeLoc hx hy hb] at h
  exact ⟨hx, hy, hb, (Option.some.inj h).symm⟩

/-- The MMA of K step `j` reads row `128 r + y`, contraction `k`, byte `byte` of an operand at the
stage byte of element `(16 j + k, y)` of the operand's tile in CTA `r` of the pair. -/
theorem mma_byteLoc_cover (L : Launch) (cta w s j : Nat) (op : TcMma.Operand)
    {r y k byte : Nat} (hsb : L.sharedBase % 128 = 0) (hr : r < 2) (hy : y < 128) (hk : k < 16)
    (hb : byte < 2) :
    (mmaSpec L cta w s j).byteLoc op (32 * (128 * r + y) + 2 * k + byte) =
      some (stageByte (cta / 2 * 2 + r)
        (L.sharedBase + stageOff s (opTile w op)) (16 * j + k) y byte) := by
  have hdiv : (32 * (128 * r + y) + 2 * k + byte) / 32 = 128 * r + y := by omega
  have hkdiv : (32 * (128 * r + y) + 2 * k + byte) / 2 % 16 = k := by omega
  have hbmod : (32 * (128 * r + y) + 2 * k + byte) % 2 = byte := by omega
  have hlocal : (128 * r + y) % 128 = y := by omega
  have hextent : 128 * r + y < 256 := by omega
  have hcta : (if 128 * r + y < 128 then cta / 2 * 2 else cta / 2 * 2 + 1) = cta / 2 * 2 + r := by
    split_ifs <;> omega
  have hvalid := mmaDescriptor_valid
  unfold mmaDescriptor at hvalid
  have hst : ∀ q, (L.sharedBase + stageOff s q) % 128 = 0 := by
    intro q; unfold stageOff; split_ifs <;> omega
  have haddr : ∀ q, TcShared.byteAddress 2 .k (stepDescriptor (L.sharedBase + stageOff s q) 0 j)
      y k byte = some (L.sharedBase + stageOff s q + TensorSwizzle.offset .b128
        (L.sharedBase + stageOff s q) (128 * y + 2 * (16 * j + k) + byte)) := by
    intro q
    rw [stepDescriptor]
    exact TcShared.k128_tma_byte 2 _ (16 * j) 0 y k byte (hst q) hb
  cases op <;>
    simp only [TcMma.OperandSpec.byteLoc, mmaSpec, mmaDescriptor, TcMma.Kind.k, TcMma.Kind.width,
      TcMma.Operand.extent, CtaGroup.size, hdiv, hvalid, hextent, and_self, not_true_eq_false,
      ↓reduceIte, TcMma.Operand.major, hlocal, hkdiv, hbmod, hcta, Option.isSome_none,
      Bool.false_eq_true, and_false, reduceCtorEq, false_and, Option.pure_def, haddr,
      stageByte, opTile] <;> ring_nf <;> rfl

/-- Every byte an MMA of K step `j` reads is the stage byte of an element of its operand's tile in
one CTA of the pair. -/
theorem mma_byteLoc (L : Launch) (cta w s j : Nat) (op : TcMma.Operand) {idx : Nat} {l : Loc}
    (hsb : L.sharedBase % 128 = 0) (h : (mmaSpec L cta w s j).byteLoc op idx = some l) :
    idx / 32 < 256 ∧ l = stageByte (cta / 2 * 2 + idx / 32 / 128)
      (L.sharedBase + stageOff s (opTile w op)) (16 * j + idx / 2 % 16)
      (idx / 32 % 128) (idx % 2) := by
  have hrow : idx / 32 < 256 := by
    by_contra hn
    have hvalid := mmaDescriptor_valid
    unfold mmaDescriptor at hvalid
    cases op <;> simp [TcMma.OperandSpec.byteLoc, mmaSpec, mmaDescriptor, TcMma.Kind.k,
      TcMma.Kind.width, TcMma.Operand.extent, hvalid] at h <;> omega
  have hidx : idx = 32 * (128 * (idx / 32 / 128) + idx / 32 % 128) + 2 * (idx / 2 % 16) + idx % 2 :=
    by
    omega
  rw [hidx, mma_byteLoc_cover L cta w s j op hsb (by omega) (by omega) (by omega) (by omega)] at h
  exact ⟨hrow, (Option.some.inj h).symm⟩

/-- The tiles lie before the staging buffers. -/
theorem stageOff_lt {s j : Nat} (hs : s < 4) (hj : j < 3) : stageOff s j + 16384 ≤ 197632 := by
  unfold stageOff; split_ifs <;> omega

/-- Distinct tiles, and distinct elements of one tile, are distinct bytes. -/
theorem stageByte_inj {sb c c' s s' j j' x x' y y' b b' : Nat}
    (hs : s < 4) (hs' : s' < 4) (hj : j < 3) (hj' : j' < 3) (hx : x < 64) (hx' : x' < 64)
    (hy : y < 128) (hy' : y' < 128) (hb : b < 2) (hb' : b' < 2)
    (h : stageByte c (sb + stageOff s j) x y b = stageByte c' (sb + stageOff s' j') x' y' b') :
    c = c' ∧ s = s' ∧ j = j' ∧ x = x' ∧ y = y' ∧ b = b' := by
  simp only [stageByte, Loc.mk.injEq, true_and] at h
  obtain ⟨hc, ha⟩ := h
  have r1 := TensorSwizzle.offset_row .b128 (sb + stageOff s j) (128 * y + 2 * x + b)
  have r2 := TensorSwizzle.offset_row .b128 (sb + stageOff s' j') (128 * y' + 2 * x' + b')
  have hst : ∀ s j, stageOff s j = 1024 + 16384 * (if j = 2 then 8 + s else j + 2 * s) := by
    intro s j; unfold stageOff; split_ifs <;> omega
  have ht : (if j = 2 then 8 + s else j + 2 * s) = (if j' = 2 then 8 + s' else j' + 2 * s') := by
    simp only [hst] at ha r1 r2
    omega
  obtain ⟨rfl, rfl⟩ : s = s' ∧ j = j' := by split_ifs at ht <;> omega
  have hoff : 128 * y + 2 * x + b = 128 * y' + 2 * x' + b' :=
    TensorSwizzle.offset_injective .b128 (sb + stageOff s j) (by omega)
  exact ⟨hc, rfl, rfl, by omega, by omega, by omega⟩

end PTX.Kernels.Fp16Gemm8192.Proof.InputRing
