-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmScoreLoads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerNumeric

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Wg0 PTX.Flow PTX.Assumption

noncomputable section

private theorem read_masked_pair (m n : Bool) (a b : ℝ) :
    pairRead (joinValue (if m then .float .f32 a else negInf)
      (if n then .float .f32 b else negInf)) =
      some (.ok (if m then (a : EReal) else ⊥, if n then (b : EReal) else ⊥)) := by
  cases m <;> cases n <;> rfl

private theorem add_masked (m : Bool) (a b : ℝ) :
    addEReal (if m then (a : EReal) else ⊥) (b : EReal) =
      some (if m then ((a + b : ℝ) : EReal) else ⊥) := by
  cases m <;> simp [addEReal, EReal.coe_add]

private theorem masked_value (m : Bool) (a : ℝ) :
    erealValue .f32 (if m then (a : EReal) else ⊥) = peakVal (if m then ↑a else ⊥) := by
  cases m
  · rfl
  · exact erealValue_coe .f32 a

/-- The packed addition joins the two QK datapath results and preserves the invalid-slot mask. -/
theorem scorePair_masked_add (m n : Bool) (lo₀ lo₁ hi₀ hi₁ : ℝ) :
    peerAddE (joinValue (if m then .float .f32 lo₀ else negInf)
      (if n then .float .f32 lo₁ else negInf))
        (.pair (.float .f32 hi₀) (.float .f32 hi₁)) =
      .ok (.pair (peakVal (if m then ↑(lo₀ + hi₀) else ⊥))
        (peakVal (if n then ↑(lo₁ + hi₁) else ⊥))) := by
  have hpeer := read_masked_pair true true hi₀ hi₁
  change pairRead (.pair (.float .f32 hi₀) (.float .f32 hi₁)) =
    some (.ok ((hi₀ : EReal), (hi₁ : EReal))) at hpeer
  simp only [peerAddE, idealAdd2, read_masked_pair, hpeer, bindRead, add_masked,
    masked_value, pure, Except.pure]

/-- When the score-load words and valid bits are identified, the computed pair is exactly
the logical block score pair used by the probability recurrence. -/
theorem scorePair_blockScore {P : Params} {L : Launch} {g : Nat}
    (d : Wg0.D) (raw : Nat → Nat → Nat) (valid : Nat → Bool) (i : Fin 16)
    (lo₀ lo₁ hi₀ hi₁ : ℝ)
    (hlo₀ : d.ownScores.getD (2 * i.val) (PTX.Proof.b32 0) = .float .f32 lo₀)
    (hlo₁ : d.ownScores.getD (2 * i.val + 1) (PTX.Proof.b32 0) = .float .f32 lo₁)
    (hm₀ : d.maskWord.toNat.testBit (2 * i.val) = valid (32 * half L g + 2 * i.val))
    (hm₁ : d.maskWord.toNat.testBit (2 * i.val + 1) = valid (32 * half L g + 2 * i.val + 1))
    (hs₀ : lo₀ + hi₀ = blockDot P L g (head L g) (32 * half L g + 2 * i.val) raw)
    (hs₁ : lo₁ + hi₁ = blockDot P L g (head L g) (32 * half L g + 2 * i.val + 1) raw) :
    peerAddE (ownScorePair d i.val) (.pair (.float .f32 hi₀) (.float .f32 hi₁)) =
      .ok (.pair (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * i.val) raw valid))
        (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * i.val + 1) raw valid))) := by
  rw [ownScorePair, ownMaskedValue, ownMaskedValue, hlo₀, hlo₁, hm₀, hm₁]
  rw [scorePair_masked_add, hs₀, hs₁]
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
