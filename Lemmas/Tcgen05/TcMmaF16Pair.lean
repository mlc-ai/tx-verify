-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

/-! # An element of a `kind::f16` MMA from its two bytes

`element_of_pair`: an element whose two bytes rebuild to a number is that number; `rebuild_number`:
the two bytes of a number do. -/

namespace PTX.TcMma
open PTX

/-- **An element whose two bytes rebuild to a number is that number.** -/
theorem element_of_pair {f o : FloatFmt} {op : Operand} {bs : List (Option Byte)} {row k : Nat}
    {b0 b1 : Option Byte} {x : ℝ} (h0 : bs[2 * (row * 16 + k)]? = some b0)
    (h1 : bs[2 * (row * 16 + k) + 1]? = some b1)
    (hx : (rebuild 1 [b0, b1] >>= valFloat f) = .ok x) :
    Assumption.idealMmaElement (.f16 f o) op bs row k = .ok x := by
  have h2 := take_two h0 h1
  have hb' : elementBytes (.f16 f o) bs row k = [b0, b1] := by
    rw [← h2]
    simp [elementBytes, Kind.k, Kind.width, Nat.mul_comm]
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb']
  exact hx

/-- The two bytes of a number rebuild to it. -/
theorem rebuild_number {f : FloatFmt} (hf : Input16 f) (x : ℝ) :
    (rebuild 1 [some ((Value.float f x).byteAt 0), some ((Value.float f x).byteAt 1)] >>=
      valFloat f) = .ok x := by
  rcases hf with rfl | rfl <;>
    simp [rebuild, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, valFloat,
      List.range_succ] <;> rfl

end PTX.TcMma
