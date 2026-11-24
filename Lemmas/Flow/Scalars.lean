-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Regs

@[expose] public section

/-! # Scalars of a site machine

A proof tool. Facts about the scalars a site machine's registers hold and the bytes a read
returns: truncation to a width is idempotent (`truncBits_idem`), the empty register state is
the state at a thread's start (`at_init`), a `32`-bit float's bytes (`fl_byte`) and its value as
`f32` (`valFloat_fl`, `valFloat_z0` for the zero bit pattern). -/

namespace PTX.Proof
open PTX

theorem truncBits_idem (w : Nat) (b : BitVec 64) : truncBits w (truncBits w b) = truncBits w b := by
  unfold truncBits
  congr 1
  have h1 : b.toNat % 2 ^ w < 2 ^ 64 := lt_of_le_of_lt (Nat.mod_le _ _) b.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_mod]

/-- The state before a thread's first instruction. -/
theorem at_init : At ({} : TState) 0 [] := ⟨rfl, rfl, rfl, rfl, by simp [Holds]⟩

theorem fl_byte (y : ℝ) {k : Nat} (hk : k < 4) : (fl y).toBytes[k]? = some (fl y, k) := by
  rw [Value.toBytes, show (fl y).bytes = 4 from rfl]
  simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some]
  rfl

theorem valFloat_fl (y : ℝ) : valFloat .f32 (fl y) = .ok y := rfl

/-- The bit pattern `0f00000000` read as `f32` is `0`. -/
theorem valFloat_z0 : valFloat .f32 (b32 0) = .ok 0 := by
  have h : FloatFmt.f32.layout.decode 0 = some (.zero false) := by
    simp [FloatFmt.layout, Layout.decode, Layout.fieldVal]
  have hc : classify .f32 (b32 0) = .ok (.zero false) := by
    simpa [b32, FloatFmt.bytes] using classify_bits (fmt := .f32) (by norm_num) h
  rw [valFloat_of_classify (fmt := .f32) (v := b32 0) (x := .zero false)
    (by intro f y hh; cases hh) hc]
  simp [FVal.finite, pure, Except.pure]

end PTX.Proof
