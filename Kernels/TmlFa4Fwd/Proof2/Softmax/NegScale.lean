-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.MaskSeg
public import Lemmas.Flow.FloatWord

@[expose] public section

/-! # The negated exponent scale (pc 4398)

After the first round's arrival at the correction warps' named barrier (pc 4397) the code negates
the exponent scale word: `neg.f32 %r170, %r6072`, where `%r6072` (register 7132) holds the word
the role loaded from parameter 12, `.bits 32 (paramW p.scaleLog2Bits)`. Core reads the word
through its pattern (`classify`), whose number the launch's `Pre` gives (`scales`: a positive
finite `f32`), and writes the negated number. `seg_sym` does not read a symbolic pattern, so the
step is proved here by Core's rule (`Seg.writes`): no assumption gives `neg` a rule and none
takes a segment at pc 4398. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The exponent scale word of the launch: a positive finite `f32` number below `2 ^ 32`. -/
theorem scale_word {p : Params} {L : Launch} {m : Mem0} (hp : Pre p L m) :
    ∃ s : ℚ, f32Value p.scaleLog2Bits = some s ∧ 0 < s ∧ p.scaleLog2Bits < 2 ^ 32 := by
  obtain ⟨s, t, hs, -, hs0, -⟩ := hp.scales
  exact ⟨s, hs, hs0, (hp.values (12, p.scaleLog2Bits) (by simp [Params.scalarWords])).1⟩

/-- **The step at pc 4398**: from facts naming the scale word, the negated scale in register
1230 (`%r170`), every fact kept. -/
theorem neg_scale {L : Launch} {g S : Nat} {s : ℚ} (hS : f32Value S = some s) (h0 : s ≠ 0)
    (h32 : S < 2 ^ 32) {F : List (Nat × Value)}
    (hF : (7132, Value.bits 32 (Epilogue.paramW S)) ∈ F)
    (hk : freshKeys [(1230, Value.float .f32 ((-s : ℚ) : ℝ))] F = true) :
    ∃ n, Seg kernel Assumptions.all L g n 4398 F 4399
      ((1230, Value.float .f32 ((-s : ℚ) : ℝ)) :: F) := by
  refine Seg.writes (dv := [(1230, Value.float .f32 ((-s : ℚ) : ℝ))]) (by code_lookup) rfl ?_ hk
  intro R cf hR
  rw [execLocalA_core (pc := 4398) (by
    intro t _ a ha
    simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) (by
    repeat' (first
      | exact PTX.Assumption.SegFreePc.nil
      | refine PTX.Assumption.SegFreePc.cons ?_ ?_)
    all_goals first
      | seg_free_elem
      | (intro L g t ht; simp only [Assumptions.swExp2, ht]; simp
         intro h; exact absurd h (by decide))) rfl]
  have hr : R 7132 = some (.bits 32 (Epilogue.paramW S)) := holds_mem hR hF
  simp [execLocal, Op.rule, FloatInstr.rule, execFloat, readValue, readReg, hr, floatLane,
    classify_word hS h0 h32, FloatInstr.lane, FloatInstr.ieee, FloatInstr.flushIn, boolCombine,
    bind, Except.bind, pure, Except.pure, FVal.negate, FVal.toValue, setRegsL]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
