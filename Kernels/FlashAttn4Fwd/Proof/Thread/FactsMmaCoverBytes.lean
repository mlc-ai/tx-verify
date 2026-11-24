-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaFootprint
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # Every byte of a ring region is an MMA step's operand byte

The 128-byte swizzle is an involution that keeps a byte's 128-byte row (`offset_involutive`,
`offset_row`), so a byte at offset `q` of a swizzled box is the image of `offset q`, whose row and
column give the operand coordinates. With the step starts of the descriptors
(`kStepStart`, `qStepStart`, `vStepStart`) and the byte formulas of the operands
(`SmemElements.qk_b_byteLoc`, `qk_a_byteLoc`, `pv_b_byteLoc`), each byte of a K slot, a Q stage or
a V slot, in either CTA of the pair, is read by some step `j < 8` at some operand index
(`Mma.k_cover`, `Mma.q_cover`, `Mma.v_cover`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch}

/-- A byte of a K-major box of `R` rows: the swizzle image of a row and a column. -/
theorem kbox_cover (base q R : Nat) (hq : q < 128 * R) :
    ∃ y < R, ∃ jj < 4, ∃ k < 16, ∃ z < 2,
      TensorSwizzle.offset .b128 base (128 * y + 2 * (16 * jj + k) + z) = q := by
  have hr := TensorSwizzle.offset_row .b128 base q
  refine ⟨TensorSwizzle.offset .b128 base q / 128, by omega,
    TensorSwizzle.offset .b128 base q % 128 / 32, by omega,
    TensorSwizzle.offset .b128 base q % 32 / 2, by omega,
    TensorSwizzle.offset .b128 base q % 2, by omega, ?_⟩
  rw [show 128 * (TensorSwizzle.offset .b128 base q / 128) +
      2 * (16 * (TensorSwizzle.offset .b128 base q % 128 / 32) +
        TensorSwizzle.offset .b128 base q % 32 / 2) + TensorSwizzle.offset .b128 base q % 2 =
      TensorSwizzle.offset .b128 base q by omega, TensorSwizzle.offset_involutive]

/-- A byte of an MN-major box of 128 rows: the swizzle image of a key row and a column. -/
theorem mnbox_cover (base q : Nat) (hq : q < 16384) :
    ∃ jv < 8, ∃ k < 16, ∃ y < 64, ∃ z < 2,
      TensorSwizzle.offset .b128 base (128 * (16 * jv + k) + 2 * y + z) = q := by
  have hr := TensorSwizzle.offset_row .b128 base q
  refine ⟨TensorSwizzle.offset .b128 base q / 128 / 16, by omega,
    TensorSwizzle.offset .b128 base q / 128 % 16, by omega,
    TensorSwizzle.offset .b128 base q % 128 / 2, by omega,
    TensorSwizzle.offset .b128 base q % 2, by omega, ?_⟩
  rw [show 128 * (16 * (TensorSwizzle.offset .b128 base q / 128 / 16) +
      TensorSwizzle.offset .b128 base q / 128 % 16) +
      2 * (TensorSwizzle.offset .b128 base q % 128 / 2) + TensorSwizzle.offset .b128 base q % 2 =
      TensorSwizzle.offset .b128 base q by omega, TensorSwizzle.offset_involutive]

/-- **A byte of a K slot** is read by some step as the B operand of a QK MMA. -/
theorem Mma.k_cover (hal : L.sharedBase % 1024 = 0) (sl : Fin 6) {a r : Nat} (ha : a < 16384)
    (hr : r < 2) :
    ∃ j : Fin 8, ∃ idx, ∀ s : OperandSpec, s.descriptor = SmemElements.qkDesc →
      s.b = kMajorDesc (kStepStart L sl j) →
      s.byteLoc .b idx = some ⟨.shared, if r = 0 then s.lowCta else s.highCta,
        L.sharedBase + (FBar.kvFull sl).regionOff + a⟩ := by
  have hsl := sl.isLt
  obtain ⟨y, hy, jj, hjj, k, hk, z, hz, hoff⟩ :=
    kbox_cover (L.sharedBase + (FBar.kvFull sl).regionOff + 8192 * (a / 8192)) (a % 8192) 64
      (by omega)
  refine ⟨⟨4 * (a / 8192) + jj, by omega⟩, 32 * (64 * r + y) + 2 * k + z, fun s hD hs => ?_⟩
  have hb : (L.sharedBase + (FBar.kvFull sl).regionOff + 8192 * (a / 8192)) % 128 = 0 := by
    simp only [FBar.regionOff]
    omega
  rw [SmemElements.qk_b_byteLoc hD (c := 16 * jj) (by
    rw [hs]
    simp only [kStepStart]
    congr 1
    omega) hb hr hy hk hz, hoff]
  congr 2
  omega

/-- **A byte of a Q stage** is read by some step as the A operand of a QK MMA. -/
theorem Mma.q_cover (hal : L.sharedBase % 1024 = 0) (st : Fin 2) {a r : Nat} (ha : a < 32768)
    (hr : r < 2) :
    ∃ j : Fin 8, ∃ idx, ∀ s : OperandSpec, s.descriptor = SmemElements.qkDesc →
      s.aTmem = none → s.a = kMajorDesc (qStepStart L st j) →
      s.byteLoc .a idx = some ⟨.shared, if r = 0 then s.lowCta else s.highCta,
        L.sharedBase + (FBar.qFull st).regionOff + a⟩ := by
  have hst := st.isLt
  obtain ⟨y, hy, jj, hjj, k, hk, z, hz, hoff⟩ :=
    kbox_cover (L.sharedBase + (FBar.qFull st).regionOff + 16384 * (a / 16384)) (a % 16384) 128
      (by omega)
  refine ⟨⟨4 * (a / 16384) + jj, by omega⟩, 32 * (128 * r + y) + 2 * k + z,
    fun s hD haT hs => ?_⟩
  have hb : (L.sharedBase + (FBar.qFull st).regionOff + 16384 * (a / 16384)) % 128 = 0 := by
    simp only [FBar.regionOff]
    omega
  rw [SmemElements.qk_a_byteLoc hD haT (c := 16 * jj) (by
    rw [hs]
    simp only [qStepStart]
    congr 1
    omega) hb hr hy hk hz, hoff]
  congr 2
  omega

/-- **A byte of a V slot** is read by some step as the B operand of a PV MMA. -/
theorem Mma.v_cover (hal : L.sharedBase % 1024 = 0) (sl : Fin 6) {a r : Nat} (ha : a < 16384)
    (hr : r < 2) :
    ∃ j : Fin 8, ∃ idx, ∀ s : OperandSpec, s.descriptor = SmemElements.pvDesc →
      s.b = mnMajorDesc (vStepStart L sl j) →
      s.byteLoc .b idx = some ⟨.shared, if r = 0 then s.lowCta else s.highCta,
        L.sharedBase + (FBar.kvFull sl).regionOff + a⟩ := by
  have hsl := sl.isLt
  obtain ⟨jv, hjv, k, hk, y, hy, z, hz, hoff⟩ :=
    mnbox_cover (L.sharedBase + (FBar.kvFull sl).regionOff) a ha
  refine ⟨⟨jv, hjv⟩, 32 * (64 * r + y) + 2 * k + z, fun s hD hs => ?_⟩
  have hb : (L.sharedBase + (FBar.kvFull sl).regionOff) % 128 = 0 := by
    simp only [FBar.regionOff]
    omega
  rw [SmemElements.pv_b_byteLoc hD (c := 16 * jv) (by
    rw [hs]
    simp only [vStepStart]
    congr 2
    omega) hb hr hy hk hz, hoff]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
