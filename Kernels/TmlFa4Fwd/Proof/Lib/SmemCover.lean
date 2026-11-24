-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.SmemElements
import Lemmas.Tensor.BoxWrite

@[expose] public section

/-! # The operands of a block of eight MMAs fill their slot

The eight A operands of a QK block fill the Q stage, its eight B operands the K slot, and the eight
B operands of a PV block the V slot, of 32768 bytes each. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Flow TcMma

/-- A byte of a 16384-byte box, by the swizzle's inverse. -/
theorem box_split {base off : Nat} (ho : off < 16384) : ∃ y c z, y < 128 ∧ c < 64 ∧ z < 2 ∧
    TensorSwizzle.offset .b128 base (128 * y + 2 * c + z) = off := by
  have hr := TensorSwizzle.offset_row .b128 base off
  have hi := TensorSwizzle.offset_involutive .b128 base off
  refine ⟨TensorSwizzle.offset .b128 base off / 128,
    TensorSwizzle.offset .b128 base off % 128 / 2, TensorSwizzle.offset .b128 base off % 2,
    by omega, by omega, by omega, ?_⟩
  rw [show 128 * (TensorSwizzle.offset .b128 base off / 128) +
    2 * (TensorSwizzle.offset .b128 base off % 128 / 2) + TensorSwizzle.offset .b128 base off % 2 =
    TensorSwizzle.offset .b128 base off by omega]
  exact hi

/-- **A byte of a QK MMA's box** is a byte of the A operand, and of the B operand, of one of its
four steps. -/
theorem qk_cover {base off : Nat} (hb : base % 128 = 0) (ho : off < 16384) :
    ∃ j < 4, ∃ index < 4096, ∀ (s : OperandSpec) (c : Nat), s.descriptor = qkDsc →
      s.lowCta = c → s.aTmem = none →
      (s.a = kDesc (base + 32 * j) → s.byteLoc .a index = some ⟨.shared, c, base + off⟩) ∧
      (s.b = kDesc (base + 32 * j) → s.byteLoc .b index = some ⟨.shared, c, base + off⟩) := by
  obtain ⟨y, cc, z, hy, hc, hz, he⟩ := box_split (base := base) ho
  refine ⟨cc / 16, by omega, 32 * y + 2 * (cc % 16) + z, by omega, fun s c hD hl haT => ?_⟩
  have hk : cc % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize hkd : cc % 16 = k at hk
  generalize hjd : cc / 16 = j
  have hcc : cc = 16 * j + k := by omega
  subst hcc
  have haddr := k_byteAddress (base := base) (c := 16 * j) (y := y) (k := k) (z := z) hb hz
  rw [show 2 * (16 * j) = 32 * j by ring, he] at haddr
  have hdiv : (32 * y + 2 * k + z) / (16 * 2) = y := by omega
  have hkdiv : (32 * y + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * y + 2 * k + z) % 2 = z := by omega
  have hv := qkDsc_valid
  constructor <;> intro hs <;> unfold OperandSpec.byteLoc <;>
  · simp only [hD, qkDsc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv, Operand.major,
      hkdiv, hbmod, hs, haT, hl] at hv ⊢
    simp [hv, hy, Nat.mod_eq_of_lt hy, haddr]

/-- **A byte of a V slot** is a byte of the B operand of one of the eight steps of a PV block. -/
theorem pv_cover {base off : Nat} (hb : base % 128 = 0) (ho : off < 32768) :
    ∃ j < 8, ∃ index < 4096, ∀ (s : OperandSpec) (c : Nat), s.descriptor = pvDsc →
      s.lowCta = c → s.b = mnDesc (base + 2048 * j) →
      s.byteLoc .b index = some ⟨.shared, c, base + off⟩ := by
  obtain ⟨rr, hr, o, ho', rfl⟩ : ∃ rr < 2, ∃ o < 16384, off = 16384 * rr + o :=
    ⟨off / 16384, by omega, off % 16384, Nat.mod_lt _ (by decide), by omega⟩
  obtain ⟨row, y, z, hrow, hy, hz, he⟩ := box_split (base := base + 16384 * rr) ho'
  refine ⟨row / 16, by omega, 32 * (64 * rr + y) + 2 * (row % 16) + z, by omega,
    fun s c hD hl hs => ?_⟩
  have hk : row % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize hkd : row % 16 = k at hk
  generalize hjd : row / 16 = j at hs
  have hrr : row = 16 * j + k := by omega
  subst hrr
  have haddr := mn_byteAddress (base := base + 2048 * j) (r := rr) (y := y) (k := k) (z := z)
    (by omega) hy hz
  have e1 := TensorSwizzle.offset_add_base .b128 (base + 2048 * j + 16384 * rr)
    (128 * k + 2 * y + z) (by omega)
  have e2 := TensorSwizzle.offset_add_base .b128 (base + 16384 * rr)
    (128 * (16 * j + k) + 2 * y + z) (by omega)
  have e3 : base + 2048 * j + 16384 * rr + (128 * k + 2 * y + z) =
      base + 16384 * rr + (128 * (16 * j + k) + 2 * y + z) := by ring
  rw [← e1, e3, e2, he] at haddr
  have hdiv : (32 * (64 * rr + y) + 2 * k + z) / (16 * 2) = 64 * rr + y := by omega
  have hkdiv : (32 * (64 * rr + y) + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * (64 * rr + y) + 2 * k + z) % 2 = z := by omega
  have hext : 64 * rr + y < 128 := by omega
  have hv := pvDsc_valid
  unfold OperandSpec.byteLoc
  simp only [hD, pvDsc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv, Operand.major,
    hkdiv, hbmod, hs, hl] at hv ⊢
  simp [hv, hext, Nat.mod_eq_of_lt hext, haddr]
  omega

end PTX.Kernels.TmlFa4Fwd.Proof.Tm
