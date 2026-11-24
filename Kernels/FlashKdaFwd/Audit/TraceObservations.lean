-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.TraceArithmetic

/-! Compare each of the three hardware carry updates, conversions, and final buffer word
to the arithmetic rules. The debugger supplies the register words. -/
namespace FlashKda.Stateless.Reconstruction
open PTX Carry Carry.Output
noncomputable section

def numeric (fmt : FloatFmt) (rows : List (List Nat)) (block column : Nat) : Option ℚ := do
  let row ← rows[block]?
  fmt.decode (← row[column]?)

def replayCarry (b : Nat) : Option ℚ := do
  let source := numeric .f32 Observed.stateFma b
  fused (← source 0) (← source 1) (← source 2)

theorem hold_fma : fused lower 1 0 = some lower := by
  have lane : carryUpdate.lane [.fin lower,.fin 1,.zero false] = some (.val (.fin lower)) := by
    apply Carry.evaluate (intermediate := .fin lower)
    · decide +kernel
    · decide +kernel
    · exact (Normalize.exactField_sound (v := .fin lower) (bits := 0x3f817fff)
        (by decide +kernel)).trans (by decide +kernel)
  unfold fused
  rw [show FVal.ofRat lower = .fin lower by decide +kernel,
    show FVal.ofRat 1 = .fin 1 by decide +kernel,show FVal.ofRat 0 = .zero false by decide +kernel,
    lane]
  rfl

/-- Each output word of the fused instruction and its following bfloat16 conversion. -/
theorem carry_trace (b : Fin 3) :
    replayCarry b = numeric .f32 Observed.updatedState b 0 ∧
    (replayCarry b).bind brain = numeric .bf16 Observed.stateSharedStore b 1 := by
  let f := numeric .f32 Observed.stateFma
  have inputs : (f 0 0, f 0 1, f 0 2) = (some 0,some 1,some (3/2)) ∧
      (f 1 0, f 1 1, f 1 2) = (some (3/2),some multiplier,some (restoredK*corrected)) ∧
      (f 2 0, f 2 1, f 2 2) = (some lower,some 1,some 0) := by decide +kernel
  have states (i a d c : ℕ) (x y z : ℚ) (h : (f i a,f i d,f i c) = (some x,some y,some z)) :
      f i a = some x ∧ f i d = some y ∧ f i c = some z := by simpa using h
  obtain ⟨a0,b0,c0⟩ := states _ _ _ _ _ _ _ inputs.1
  obtain ⟨a1,b1,c1⟩ := states _ _ _ _ _ _ _ inputs.2.1
  obtain ⟨a2,b2,c2⟩ := states _ _ _ _ _ _ _ inputs.2.2
  have v0 : brain (3/2) = some (3/2) :=
    brain_field (w := 0x3fc0) (by decide) (by decide) (by decide +kernel)
  have v1 : brain lower = some (129/128) := by simp [brain,next_tile_views.1,FVal.num]
  have replay0 : replayCarry 0 = some (3/2) := by
    change (do fused (← f 0 0) (← f 0 1) (← f 0 2)) = _
    simp [a0,b0,c0,first_fma]
  have replay1 : replayCarry 1 = some lower := by
    change (do fused (← f 1 0) (← f 1 1) (← f 1 2)) = _
    simp [a1,b1,c1,second_fma]
  have replay2 : replayCarry 2 = some lower := by
    change (do fused (← f 2 0) (← f 2 1) (← f 2 2)) = _
    simp [a2,b2,c2,hold_fma]
  fin_cases b
  · change replayCarry 0 = _ ∧ (replayCarry 0).bind brain = _
    rw [replay0]
    change _ ∧ brain (3/2) = _
    rw [v0]; decide +kernel
  · change replayCarry 1 = _ ∧ (replayCarry 1).bind brain = _
    rw [replay1]
    change _ ∧ brain lower = _
    rw [v1]; decide +kernel
  · change replayCarry 2 = _ ∧ (replayCarry 2).bind brain = _
    rw [replay2]
    change _ ∧ brain lower = _
    rw [v1]; decide +kernel

/-- For the recorded output tensor the unique live word, both final output accumulators
and the selected halfword before and after the shared-to-global transfer agree. -/
theorem publication :
    forward = numeric .f32 Observed.outputAccumulator 2 0 ∧
    forward = numeric .f32 Observed.outputConversion 2 0 ∧
    forward = numeric .bf16 Observed.outputSharedStore 2 1 ∧
    forward = numeric .bf16 Observed.beforeGlobalStore 0 0 ∧
    forward = FloatFmt.bf16.decode Observed.finalMemory ∧
    forward = FloatFmt.bf16.decode Observed.publicWord ∧
    FloatFmt.bf16.decode Observed.initialMemory = some (-7) ∧
    Observed.outputOffset = 32 * 128 * 2 := by rw [reconstructed]; decide +kernel

end
end FlashKda.Stateless.Reconstruction
