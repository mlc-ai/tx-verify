-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.Base

@[expose] public section

/-! # The LSE stores: the scale and the stops

The softmax scale's real number (`scale_read`) and a state that stops on every event (`stop_ok`),
for the step files of the LSE stores (`StepsLse.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

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

/-- A state whose successor is a stop for every event. -/
theorem stop_ok {d : D} (h : ∀ e, (code p L g).next d e = some none) : (code p L g).StepOk d :=
  ⟨fun _ _ _ _ _ => .inl (.inl (h _))⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
