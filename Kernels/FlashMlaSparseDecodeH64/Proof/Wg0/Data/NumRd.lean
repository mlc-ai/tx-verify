-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumMask
public import Lemmas.Flow.W0Reads

@[expose] public section

/-! # Values that read as an extended real

`Rd v x`: the value `v` is a clean four-byte word that reads as the extended real `x`, a real or
`-inf` ("reads as", valid rows). The numeric stages of the block (peer sums, row maximum, vote,
exponentials) are stated with it: the value of a register of a run is `Rd` of the extended real
the reference computes. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

theorem rd_erealValue {x : EReal} (h : SK.ni.Lane x) : Rd (erealValue .f32 x) x := by
  have hne : x ≠ ⊤ := by
    rcases h with ⟨r, rfl⟩ | rfl
    · exact EReal.coe_ne_top r
    · exact bot_ne_top
  have hh := SK.has_erealValue h
  refine ⟨?_, readEReal_erealValue hne, h⟩
  exact SK.clean hh

theorem rd_negInf : Rd negInf32 ⊥ := by
  rw [← erealValue_bot]; exact rd_erealValue (.inr rfl)

theorem rd_float (r : ℝ) : Rd (.float .f32 r) (r : EReal) := by
  rw [← erealValue_coe .f32 r]; exact rd_erealValue (.inl ⟨r, rfl⟩)

theorem rd_of_valFloat {v : Value} {r : ℝ} (hc : Clean v) (h : valFloat .f32 v = .ok r) :
    Rd v (r : EReal) := ⟨hc, readEReal_of_valFloat h, .inl ⟨r, rfl⟩⟩

/-- A pair of two words that read as `x` and `y`. -/
theorem pairRead_pair {a b : Value} {x y : EReal} (ha : Rd a x) (hb : Rd b y) :
    pairRead (.pair a b) = some (.ok (x, y)) :=
  pairRead_of_reads (by simpa [splitValue] using rd_read ha)
    (by simpa [splitValue] using rd_read hb)

/-- The join of two clean words reads as the pair. -/
theorem pairRead_join {a b : Value} {x y : EReal} (ha : Rd a x) (hb : Rd b y) :
    pairRead (joinValue a b) = some (.ok (x, y)) :=
  pairRead_of_reads (by rw [split_join_clean ha.1 hb.1]; exact rd_read ha)
    (by rw [split_join_clean ha.1 hb.1]; exact rd_read hb)

theorem split_pair_fst (a b : Value) : (splitValue 64 (.pair a b)).1 = a := rfl
theorem split_pair_snd (a b : Value) : (splitValue 64 (.pair a b)).2 = b := rfl

/-- The sum of a lane and a real is a lane (`⊥` stays `⊥`). -/
theorem lane_add_coe {x : EReal} (h : SK.ni.Lane x) (y : ℝ) :
    SK.ni.Lane (x + (y : EReal)) ∧ addEReal x (y : EReal) = some (x + (y : EReal)) := by
  rcases h with ⟨r, rfl⟩ | rfl
  · refine ⟨.inl ⟨r + y, by push_cast; rfl⟩, ?_⟩
    rw [addEReal_coe]; rfl
  · refine ⟨.inr (by simp), ?_⟩
    unfold addEReal
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp))]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
