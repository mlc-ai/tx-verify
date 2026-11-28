-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Trace
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.ScaleVals

@[expose] public section

/-! # The bytes of the scale word

The sixteen scale bytes of a row (`scaleWordOf`, element 0 lowest) are the bytes of the four words
the scale loads read: byte `4 w + b` is byte `b` of word `w` (`scaleWordOf_byte`). A 32-bit word
read is below `2 ^ 32` (`readWord_lt32`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX Numeric.Dequant

noncomputable section

/-- A 32-bit word a read event rebuilds to is below `2 ^ 32`. -/
theorem readWord_lt32 {e : Event} {y : Nat} (h : readWord 32 e = some y) : y < 2 ^ 32 :=
  Dequant.Data.bitsWord_lt (n := 32) (by rw [← Dequant.Data.readWord_eq]; exact h)

/-- **Byte `4 w + b` of the scale bytes of four loads is byte `b` of load `w`'s word.** -/
theorem scaleWordOf_byte {e0 e1 e2 e3 : Event} {y0 y1 y2 y3 : Nat}
    (h0 : readWord 32 e0 = some y0) (h1 : readWord 32 e1 = some y1)
    (h2 : readWord 32 e2 = some y2) (h3 : readWord 32 e3 = some y3) {w b : Nat} (hw : w < 4)
    (hb : b < 4) :
    byteAt (scaleWordOf [e0, e1, e2, e3]) (4 * w + b) = byteAt ([y0, y1, y2, y3].getD w 0) b := by
  have l0 := readWord_lt32 h0
  have l1 := readWord_lt32 h1
  have l2 := readWord_lt32 h2
  have hs : scaleWordOf [e0, e1, e2, e3] = Dequant.scWord y0 y1 y2 y3 := by
    simp only [scaleWordOf, h0, h1, h2, h3, Option.getD_some, Dequant.scWord]
  rw [hs]
  have h4 := Dequant.byteAt_scWord (w0 := y0) (w1 := y1) (w2 := y2) (w3 := y3) l0 l1 l2 b hb
  obtain ⟨c0, c1, c2, c3⟩ := h4
  interval_cases w
  · simpa using c0
  · rw [show 4 * 1 + b = 4 + b by omega]; simpa using c1
  · rw [show 4 * 2 + b = 4 + (4 + b) by omega]; simpa using c2
  · rw [show 4 * 3 + b = 4 + (4 + (4 + b)) by omega]; simpa using c3

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
