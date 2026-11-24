-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.GenRules
public import Kernels.TmlFa4Fwd.Proof2.Softmax.Data

@[expose] public section

/-! # A bias product's value

The first round's product of bias pair `j` (pcs 3593 to 3849, `Gen/Prod1.lean`): two `bf16` bias
halves widened (`widenE`), packed, multiplied by the bias scale's pair and added to the score pair
(`fma2E`). On halves recorded as payloads or the masked pattern (`hv16`) and the bias scale word
(a positive real) the value is the pair of the products' closed forms: the scaled bias plus the
score, or `-∞` for a masked half (`prod_eq`, the form `mask_max` reads). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- A product lane: the number `y` when the bias half is a payload, else `-∞`. -/
abbrev bvl (b : Bool) (y : ℝ) : Value :=
  if b = true then .float .f32 y else .bits 32 (BitVec.ofNat 64 4286578688)

theorem widenE_hv16 (b : Bool) (r : ℝ) :
    okVal (.bits 32 0) (Gen.widenE [hv16 b r]) = bvl b r := by
  cases b
  · show okVal _ (Gen.widenE [.bits 16 (BitVec.ofNat 64 0xFF80)]) = _
    simp only [Gen.widenE, Gen.finBf_mask, bindRead, Option.getD_none, coreWidenBf_negInf]
    rfl
  · show okVal _ (Gen.widenE [.float .bf16 r]) = _
    simp only [Gen.widenE, Gen.finBf_float, bindRead, Option.getD_some]
    rfl

theorem bvl_clean (b : Bool) (y : ℝ) : Clean (bvl b y) := by
  cases b
  · exact clean_negInf
  · exact clean_float y

theorem bvl_read (b : Bool) (y : ℝ) :
    readEReal .f32 (bvl b y) = some (.ok (if b = true then (y : EReal) else ⊥)) := by
  cases b
  · exact readEReal_negInf
  · exact readEReal_float y

theorem fma_lane {b : Bool} {r t x : ℝ} (ht : 0 < t) :
    (mulEReal (if b = true then (r : EReal) else ⊥) (t : EReal)).bind (addEReal · (x : EReal)) =
      some (if b = true then ((r * t + x : ℝ) : EReal) else ⊥) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, mulEReal_bot_pos ht, Option.bind_some]
    simp [addEReal]
  · simp only [↓reduceIte, mulEReal_coe, Option.bind_some, addEReal_coe]

theorem erealValue_bvl (b : Bool) (y : ℝ) :
    erealValue .f32 (if b = true then (y : EReal) else ⊥) = bvl b y := by
  cases b
  · exact erealValue_bot
  · exact erealValue_coe _ _

/-- **A bias product pair.** -/
theorem prod_eq {b0 b1 : Bool} {r0 r1 x0 x1 t : ℝ} {S : Value} (ht : 0 < t) (hS : Clean S)
    (hSr : readEReal .f32 S = some (.ok (t : EReal))) :
    okVal (.bits 64 0) (fma2E (joinValue (okVal (.bits 32 0) (Gen.widenE [hv16 b0 r0]))
      (okVal (.bits 32 0) (Gen.widenE [hv16 b1 r1]))) (joinValue S S)
      (.pair (.float .f32 x0) (.float .f32 x1))) =
    .pair (bvl b0 (r0 * t + x0)) (bvl b1 (r1 * t + x1)) := by
  rw [widenE_hv16, widenE_hv16]
  have h1 := split_join_clean (bvl_clean b0 r0) (bvl_clean b1 r1)
  have h2 := split_join_clean hS hS
  have hp1 : pairRead (joinValue (bvl b0 r0) (bvl b1 r1)) = some (.ok (_, _)) :=
    pairRead_of_reads (by rw [h1]; exact bvl_read b0 r0) (by rw [h1]; exact bvl_read b1 r1)
  have hp2 : pairRead (joinValue S S) = some (.ok ((t : EReal), (t : EReal))) :=
    pairRead_of_reads (by rw [h2]; exact hSr) (by rw [h2]; exact hSr)
  have hp3 : pairRead (.pair (.float .f32 x0) (.float .f32 x1)) =
      some (.ok ((x0 : EReal), (x1 : EReal))) :=
    pairRead_of_reads (readEReal_float x0) (readEReal_float x1)
  rw [fma2E_reads hp1 hp2 hp3 (fma_lane ht) (fma_lane ht), erealValue_bvl, erealValue_bvl]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
