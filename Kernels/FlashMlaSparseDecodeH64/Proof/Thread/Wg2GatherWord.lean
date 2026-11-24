-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GatherInput

@[expose] public section

/-! # The bytes of a gathered row survive little-endian reconstruction -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Proof Numeric

/-- The logical row includes zero fill for an invalid slot. -/
def gatheredByte (P : Params) (L : Launch) (g block pos off : Nat) : Nat :=
  let batch := Wg1Tma.eOf L g
  let query := Wg1Tma.qOf L g
  let extra := FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen batch)
  let slot := slotPos (P.topkLen batch) block (pos / 2) (pos % 2)
  if Wg1Tma.validBit P L g block (pos / 2) (pos % 2) then
    rowBytes P batch query extra slot off
  else 0

/-- The same logical row is selected by every lane in the CTA. -/
theorem gatheredByte_same_cta {P : Params} {L : Launch} {g h block pos off : Nat}
    (hc : ctaOf L g = ctaOf L h) :
    gatheredByte P L g block pos off = gatheredByte P L h block pos off := by
  simp only [gatheredByte, Wg1Tma.validBit, Wg1Tma.slotIdx,
    Wg1Tma.eOf, Wg1Tma.qOf, ctaidX, ctaidY, hc]
  rfl

private theorem gatheredByte_lt (P : Params) (L : Launch) (g block pos off : Nat) :
    gatheredByte P L g block pos off < 256 := by
  unfold gatheredByte
  split
  · unfold rowBytes
    dsimp only
    split <;> exact Fin.isLt _
  · decide

private theorem gatheredInput_bits (P : Params) (L : Launch) (g block pos off : Nat) :
    ∃ byte, gatheredInput P L g block pos off = some byte ∧
      byteBits byte = some (gatheredByte P L g block pos off) := by
  cases hv : Wg1Tma.validBit P L g block (pos / 2) (pos % 2)
  · have hmod : off % 4 < 4 := Nat.mod_lt _ (by decide)
    refine ⟨(b32 0, off % 4), by simp [gatheredInput, hv], ?_⟩
    simp [gatheredByte, hv, byteBits, b32, Value.bytes, Value.bitPattern, hmod,
      Bind.bind, Pure.pure]
  · let n := rowBytes P (Wg1Tma.eOf L g) (Wg1Tma.qOf L g)
      (FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen (Wg1Tma.eOf L g)))
      (slotPos (P.topkLen (Wg1Tma.eOf L g)) block (pos / 2) (pos % 2)) off
    have hValue : gatheredByte P L g block pos off = n := by simp [gatheredByte, hv, n]
    have hFit : n < 256 := hValue ▸ gatheredByte_lt P L g block pos off
    refine ⟨(.bits 8 (BitVec.ofNat 64 n), 0), by simp [gatheredInput, hv, inputByte, n], ?_⟩
    rw [hValue]
    simp [byteBits, Value.bytes, Value.bitPattern, Bind.bind, Pure.pure,
      Nat.mod_eq_of_lt hFit]

private theorem littleEndian_present {bs : List (Option Byte)} {bytes : Nat → Nat}
    (fits : ∀ k < bs.length, bytes k < 256)
    (loaded : ∀ k < bs.length, ∃ b, bs[k]? = some (some b) ∧ byteBits b = some (bytes k)) :
    ∃ w, littleEndianBits bs = some w ∧ w < 256 ^ bs.length ∧
      ∀ k < bs.length, Numeric.byteAt w k = bytes k := by
  induction bs generalizing bytes with
  | nil => exact ⟨0, rfl, by decide, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | cons item bs ih =>
    obtain ⟨b, hb, hBits⟩ := loaded 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
    subst item
    have hTail (k : Nat) (hk : k < bs.length) :
        ∃ b, bs[k]? = some (some b) ∧ byteBits b = some (bytes (k + 1)) := by
      simpa only [List.getElem?_cons_succ] using loaded (k + 1) (by simp; omega)
    obtain ⟨w, hw, hW, hUnpack⟩ := ih (bytes := fun k => bytes (k + 1))
      (fun k hk => fits (k + 1) (by simp; omega)) hTail
    have hFirst := fits 0 (by simp)
    refine ⟨bytes 0 + 256 * w, ?_, ?_, ?_⟩
    · simp [littleEndianBits, hBits, hw, Bind.bind, Pure.pure]
    · rw [List.length_cons, pow_succ']
      omega
    · intro k hk
      cases k with
      | zero =>
        simp only [Numeric.byteAt, pow_zero, Nat.div_one]
        omega
      | succ k =>
        simp only [Numeric.byteAt, pow_succ', ← Nat.div_div_eq_div_mul]
        have hDiv : (bytes 0 + 256 * w) / 256 = w := by omega
        rw [hDiv]
        exact hUnpack k (by simp at hk; omega)

/-- Reconstructing actual bytes of a gathered word returns exactly its numerical byte values. -/
theorem unpack_gathered_word {bs : List (Option Byte)} {P : Params} {L : Launch}
    {g block pos off : Nat}
    (hBytes : ∀ k < bs.length, bs[k]? = some (gatheredInput P L g block pos (off + k))) :
    bytesNat bs < 256 ^ bs.length ∧
      ∀ k < bs.length, Numeric.byteAt (bytesNat bs) k = gatheredByte P L g block pos (off + k) := by
  obtain ⟨w, hBits, hWord, hUnpack⟩ :=
    littleEndian_present (bytes := fun k => gatheredByte P L g block pos (off + k))
      (fun k _ => gatheredByte_lt P L g block pos (off + k)) (by
        intro k hk
        obtain ⟨b, hb, hv⟩ := gatheredInput_bits P L g block pos (off + k)
        exact ⟨b, (hBytes k hk).trans (congrArg some hb), hv⟩)
  simpa only [bytesNat, hBits, Option.getD_some] using ⟨hWord, hUnpack⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
