-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RawArith

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

/-- A `mul.lo.s32` of two registers; an operand without an integer reading ends the thread. -/
theorem mulStep {L : Launch} {g pc : Nat} {dst a b : Nat} {F G : List (Nat × Value)}
    {va vb : Value}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.mul .lo, .int .s 32, false, [some dst],
      [.reg a, .reg b]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false)
    (ha : (a, va) ∈ F) (hb : (b, vb) ∈ F)
    (hwrite : ∀ R, Holds R F → Holds (Function.update R dst (some (.bits 32
      (truncBits 32 (word va * word vb))))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  apply scalarStepU hc rfl rfl hs
  · intro t u hF he
    simp only [execInt, DType.width, bind, Except.bind, pure, Except.pure] at he
    cases h1 : readBits L g t 32 (.reg a) <;> rw [h1] at he <;> try contradiction
    cases h2 : readBits L g t 32 (.reg b) <;> rw [h2] at he <;> try contradiction
    rw [readBits_eq_pattern (holds_mem hF ha) h1,
      readBits_eq_pattern (holds_mem hF hb) h2] at he
    exact (Except.ok.inj he).symm
  · exact hwrite

end PTX.Kernels.InklingRelDecode.Proof.Lib
