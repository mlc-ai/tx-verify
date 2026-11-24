-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Kernels.TmlFa4Fwd.Proof.Softmax.NegScale
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The two scale words and the bias products

The exponent scale (parameter word 12, `scl`) and the bias scale (parameter word 14, `s14`) as
the steps read them (their words classify as positive finite numbers, `Pre.scales`). A bias
product of the current round (`bpf`, `bps`, `Data.lean`) reads half `n mod 8` of bias load
`n / 8`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The exponent scale as the role's table states it: its word classifies as the number
`scl p`, which is positive. -/
theorem scl_word (hp : Pre p L m) :
    classify .f32 (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.scaleLog2Bits))) =
      .ok (.fin (scl p)) ∧ (0 : ℝ) < (scl p : ℝ) := by
  obtain ⟨s, hS, hs0, h32⟩ := scale_word hp
  have hsc : scl p = s := by simp [scl, hS]
  rw [hsc]
  exact ⟨classify_word hS hs0.ne' h32, by exact_mod_cast hs0⟩

theorem s14_word (hp : Pre p L m) :
    classify .f32 (.bits 32 (truncBits 32 (BitVec.ofNat 64 p.invScaleBits))) =
      .ok (.fin (s14 p)) ∧ (0 : ℝ) < (s14 p : ℝ) := by
  obtain ⟨s, t, -, ht, -, ht0⟩ := hp.scales
  have h32 := (hp.values (14, p.invScaleBits) (by simp [Params.scalarWords])).1
  have hsc : s14 p = t := by simp [s14, ht]
  rw [hsc]
  exact ⟨classify_word ht ht0.ne' h32, by exact_mod_cast ht0⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
