-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # The 16 query copies cover the tile

Surjectivity beside `MmaFoot.copy_foot`: every byte of `[B, B + 65536)` of a CTA is a source byte
of one of the 16 copies `keyDesc B k` (`copy_cover`), and a B byte of one of the 16 QK MMAs
(`key_cover`). The 128-byte swizzle is an involution
within a 128-byte row, so the preimage of a byte is found by swizzling it once. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
open PTX

/-- **Every byte of `[B, B + 65536)` is a source byte of one of the 16 copies.** -/
theorem copy_cover {B cta a : Nat} (hB : B % 128 = 0) (hlo : B ≤ a) (hhi : a < B + 65536) :
    ∃ k idx, k < 16 ∧ idx < 4096 ∧
      TcCopy.byteLoc .s128x256b (keyDesc B k) cta idx = some ⟨.shared, cta, a⟩ := by
  have hrow := TensorSwizzle.offset_row .b128 0 a
  obtain ⟨u, hu⟩ : ∃ u, u = TensorSwizzle.offset .b128 0 a := ⟨_, rfl⟩
  rw [← hu] at hrow
  have hinv : TensorSwizzle.offset .b128 0 u = a := by
    rw [hu, TensorSwizzle.offset_involutive]
  have hu1 : B ≤ u := by omega
  have hu2 : u < B + 65536 := by omega
  refine ⟨4 * ((u - B) / 16384) + (u - B) % 128 / 32,
    32 * ((u - B) / 128 % 128) + (u - B) % 32, by omega, by omega, ?_⟩
  have hlt : 32 * ((u - B) / 128 % 128) + (u - B) % 32 < TcCpShape.s128x256b.sourceBytes := by
    simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]; omega
  unfold TcCopy.byteLoc TcShared.byteAddress
  simp [keyDesc, hlt]
  simp only [TcShared.linear, TcShared.Swizzle.sectors, TcCpShape.rowBytes, qkDelta,
    reduceCtorEq, ↓reduceIte]
  have : B + 16 * (1024 * ((4 * ((u - B) / 16384) + (u - B) % 128 / 32) / 4) +
      2 * ((4 * ((u - B) / 16384) + (u - B) % 128 / 32) % 4)) +
      (16 * 8 * ((32 * ((u - B) / 128 % 128) + (u - B) % 32) / 32 % 8) +
        1024 * ((32 * ((u - B) / 128 % 128) + (u - B) % 32) / 32 / 8) +
        1 * ((32 * ((u - B) / 128 % 128) + (u - B) % 32) % 32)) = u := by omega
  rw [this]
  exact hinv

/-- **Every byte of `[B, B + 65536)` is a B byte of the QK MMA `k`** whose B descriptor is
`keyDesc B k`, for some `k < 16` (the 16 MMAs read 4096 bytes each). -/
theorem key_cover {B a : Nat} (hB : B % 128 = 0) (hlo : B ≤ a) (hhi : a < B + 65536) :
    ∃ k, k < 16 ∧ ∀ {s : TcMma.OperandSpec}, s.descriptor = qkD → s.b = keyDesc B k →
      ∃ idx, s.byteLoc .b idx = some ⟨.shared, s.lowCta, a⟩ := by
  have hrow := TensorSwizzle.offset_row .b128 0 a
  obtain ⟨u, hu⟩ : ∃ u, u = TensorSwizzle.offset .b128 0 a := ⟨_, rfl⟩
  rw [← hu] at hrow
  have hinv : TensorSwizzle.offset .b128 0 u = a := by
    rw [hu, TensorSwizzle.offset_involutive]
  have hu1 : B ≤ u := by omega
  have hu2 : u < B + 65536 := by omega
  refine ⟨4 * ((u - B) / 16384) + (u - B) % 128 / 32, by omega, fun {s} hD hs => ?_⟩
  refine ⟨32 * ((u - B) / 128 % 128) + (u - B) % 32, ?_⟩
  have hv := qkD_valid
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width]
  simp only [qkD] at hv
  simp [hv]
  refine ⟨by omega, ?_⟩
  have hlt : (32 * ((u - B) / 128 % 128) + (u - B) % 32) / 32 < 128 := by omega
  rw [ite_eq_left hlt]
  unfold TcShared.byteAddress
  simp [keyDesc]
  simp only [TcShared.linear, TcShared.Swizzle.sectors, qkDelta, reduceCtorEq, ↓reduceIte]
  rw [ite_eq_left (by omega), Option.bind_some]
  have key : ∀ x, x = u → TcShared.Swizzle.b128.offset x = a := fun x hx => by
    subst hx
    exact hinv
  rw [key]
  omega
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
