-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.TcMma

/-- The 16-bit zero reads as the bf16 number 0. -/
theorem valFloat_bf16_zero : valFloat .bf16 (.bits 16 (BitVec.ofNat 64 0)) = .ok 0 := by
  have h : FloatFmt.bf16.layout.decode 0 = some (.zero false) := by
    simp [FloatFmt.layout, Layout.decode, Layout.fieldVal]
  have hc : classify .bf16 (.bits 16 (BitVec.ofNat 64 0)) = .ok (.zero false) := by
    simpa [FloatFmt.bytes] using classify_bits (fmt := .bf16) (n := 0) (by norm_num) h
  rw [valFloat_of_classify (fmt := .bf16) (x := .zero false) (by intro f y hh; cases hh) hc]
  simp [FVal.finite, pure, Except.pure]

/-- **An element whose two bytes are a half of the 32-bit zero is the bf16 number 0.** -/
theorem zero_elem {o : FloatFmt} {op : Operand} {bytes : List (Option Byte)} {row k p : Nat}
    (hp : p = 0 ∨ p = 2)
    (h0 : bytes[2 * (row * 16 + k)]? = some (some (.bits 32 (BitVec.ofNat 64 0), p)))
    (h1 : bytes[2 * (row * 16 + k) + 1]? = some (some (.bits 32 (BitVec.ofNat 64 0), p + 1))) :
    Assumption.idealMmaElement (.f16 .bf16 o) op bytes row k = .ok 0 := by
  have hb : elementBytes (.f16 .bf16 o) bytes row k =
      [some (.bits 32 (BitVec.ofNat 64 0), p), some (.bits 32 (BitVec.ofNat 64 0), p + 1)] := by
    rw [← take_two h0 h1]
    simp [elementBytes, Kind.k, Kind.width, Nat.mul_comm]
  have hr : rebuild 1 [some ((Value.bits 32 (BitVec.ofNat 64 0)), p),
      some ((Value.bits 32 (BitVec.ofNat 64 0)), p + 1)] = .ok (.bits 16 (BitVec.ofNat 64 0)) := by
    rcases hp with rfl | rfl <;>
      simp [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte,
        Value.bitPattern, Value.bytes, Value.toBytes, Value.byteAt] <;> rfl
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb, hr]
  exact valFloat_bf16_zero

end PTX.Kernels.InklingRelDecode.Proof.Lib
