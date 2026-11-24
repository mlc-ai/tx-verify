-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The LSE stores: the scale and the stops

The softmax scale's real number (`scale_read`) and a state that stops on every event (`stop_ok`),
for the step files of the LSE stores (`StepsLse.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The LSE's floating `selp`s write conditional values. -/
scoped macro_rules | `(tactic| sym_selp_value) => `(tactic| skip)

/-- The softmax scale's pattern reads as its real number. -/
theorem scale_read (hp : Pre p L m) :
    PTX.Assumption.readEReal .f32 (.bits 32 (Epilogue.paramW p.scaleLog2Bits)) =
      some (Except.ok ((scaleR p : ℝ) : EReal)) := by
  obtain ⟨s, t, hs, -⟩ := hp.scales
  have hb := (hp.values (12, p.scaleLog2Bits) (by simp [Params.scalarWords])).1
  have hw : Epilogue.paramW p.scaleLog2Bits = BitVec.ofNat 64 p.scaleLog2Bits :=
    truncBits_ofNat hb (by decide)
  rw [readEReal_bits32 p.scaleLog2Bits s hw (by omega) hs]
  simp [scaleR, hs]

theorem scale_pos (hp : Pre p L m) : 0 < scaleR p := by
  obtain ⟨s, t, hs, -, hpos, -⟩ := hp.scales
  simpa [scaleR, hs] using hpos

/-- The softmax scale times a row maximum: the scale is not zero. -/
theorem scale_mul (hp : Pre p L m) (x : EReal) :
    Assumption.mulEReal ((scaleR p : ℝ) : EReal) x = some (scaleR p * x) := by
  have h := scale_pos hp
  simp [Assumption.mulEReal, h.ne']

/-- A scaled row maximum is below `+∞`. -/
theorem scaled_ne_top (hp : Pre p L m) (x : Mx) : (scaleR p : EReal) * x.1 ≠ ⊤ := by
  obtain ⟨x, hx⟩ := x
  induction x using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos (scale_pos hp)]
  | coe x => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

/-- Plus the logarithm of a positive row sum. -/
theorem add_log (x : EReal) (r : ℝ) : Assumption.addEReal x (r : EReal) = some (x + r) := by
  simp [Assumption.addEReal]

/-- Plus the logarithm of a zero row sum, `-∞`. -/
theorem add_log_bot (hp : Pre p L m) (x : Mx) :
    Assumption.addEReal ((scaleR p : EReal) * x.1) ⊥ = some ⊥ := by
  simp [Assumption.addEReal, scaled_ne_top hp x]

/-- Times the constant. -/
theorem mul_ln2 (x : EReal) : Assumption.mulEReal x ((ln2F : ℝ) : EReal) = some (x * ln2F) := by
  have h : ((ln2F : ℝ) : EReal) ≠ 0 := by rw [Ne, EReal.coe_eq_zero]; norm_num
  simp [Assumption.mulEReal, h]

/-- A state whose successor is a stop for every event. -/
theorem stop_ok {d : D} (h : ∀ e, (code p L g).next d e = some none) : (code p L g).StepOk d :=
  ⟨fun _ _ _ _ _ => .inl (.inl (h _))⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
