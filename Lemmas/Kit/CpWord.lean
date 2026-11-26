-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TmemStore
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # The bytes of a copy's word

A `tcgen05.cp` word is the four consecutive source bytes, each as a one-byte slice. When a source
byte is byte `z` of a float value, the word's byte at the same position is that byte again
(`word_byteAt`), and the word has four bytes. -/

namespace PTX.Kit
open PTX

/-- **A word's byte at `u` is its source byte `u`** when the four source bytes are bytes of float
values. -/
theorem word_byteAt {s : TcCpShape} {bytes : List (Option Byte)} {row col : Nat} {v : Value}
    (h : TcCopy.word s bytes row col = some v)
    (hf : ∀ u < 4, ∃ f x z, bytes.getD (row * s.rowBytes + 4 * col + u) none =
      some ((Value.float f x).byteAt z)) :
    v.bytes = 4 ∧ ∀ u < 4, ∃ f x z, bytes.getD (row * s.rowBytes + 4 * col + u) none =
      some ((Value.float f x).byteAt z) ∧ v.byteAt u = (Value.float f x).byteAt z := by
  obtain ⟨f0, x0, z0, h0⟩ := hf 0 (by decide)
  obtain ⟨f1, x1, z1, h1⟩ := hf 1 (by decide)
  obtain ⟨f2, x2, z2, h2⟩ := hf 2 (by decide)
  obtain ⟨f3, x3, z3, h3⟩ := hf 3 (by decide)
  have k0 := h0
  have k1 := h1
  have k2 := h2
  have k3 := h3
  simp only [List.getD_eq_getElem?_getD, Nat.add_zero] at k0 k1 k2 k3
  simp [TcCopy.word, k0, k1, k2, k3] at h
  subst h
  refine ⟨by simp [Value.bytes, TcCopy.byteValue], fun u hu => ?_⟩
  interval_cases u
  · exact ⟨f0, x0, z0, h0, by simp [Value.byteAt, Value.bytes, TcCopy.byteValue]⟩
  · exact ⟨f1, x1, z1, h1, by simp [Value.byteAt, Value.bytes, TcCopy.byteValue]⟩
  · exact ⟨f2, x2, z2, h2, by simp [Value.byteAt, Value.bytes, TcCopy.byteValue]⟩
  · exact ⟨f3, x3, z3, h3, by simp [Value.byteAt, Value.bytes, TcCopy.byteValue]⟩

end PTX.Kit
