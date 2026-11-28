-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.MulStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g pc dst a : Nat} {F G : List (Nat × Value)}

/-- An `and.b32` of a register and an immediate. -/
theorem andStep {va : Value} {k : Int}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.and, .int .b 32, false, [some dst],
      [.reg a, .imm k]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false) (ha : (a, va) ∈ F)
    (hwrite : ∀ R, Holds R F → Holds (Function.update R dst (some (.bits 32
      (word va &&& truncBits 32 (BitVec.ofInt 64 k))))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  apply scalarStepU hc rfl rfl hs
  · intro t u hF he
    have himm : readBits L g t 32 (.imm k) = .ok (truncBits 32 (BitVec.ofInt 64 k)) := rfl
    simp only [execInt, DType.width, bind, Except.bind, pure, Except.pure, himm,
      show (32 = 1) = False by decide, ite_false] at he
    cases h1 : readBits L g t 32 (.reg a) <;> rw [h1] at he <;> try contradiction
    rw [readBits_eq_pattern (holds_mem hF ha) h1] at he
    exact (Except.ok.inj he).symm
  · exact hwrite

/-- A `shl.b32` of a register by an immediate below 32. -/
theorem shlStep {va : Value} {k : Int} {n : Nat}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.shl, .int .b 32, false, [some dst],
      [.reg a, .imm k]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false) (ha : (a, va) ∈ F)
    (hk : (truncBits 32 (BitVec.ofInt 64 k)).toNat = n) (hn : n < 32)
    (hwrite : ∀ R, Holds R F → Holds (Function.update R dst (some (.bits 32
      (truncBits 32 (word va <<< n))))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  apply scalarStepU hc rfl rfl hs
  · intro t u hF he
    have himm : readBits L g t 32 (.imm k) = .ok (truncBits 32 (BitVec.ofInt 64 k)) := rfl
    simp only [execInt, DType.width, bind, Except.bind, pure, Except.pure, himm] at he
    cases h1 : readBits L g t 32 (.reg a) <;> rw [h1] at he <;> try contradiction
    rw [readBits_eq_pattern (holds_mem hF ha) h1] at he
    simp only [hk, not_le.mpr hn, ite_false] at he
    exact (Except.ok.inj he).symm
  · exact hwrite

/-- An `add.s32` of two registers that hold 32-bit words. -/
theorem addBitsStep {b : Nat} {x y : BitVec 64}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      [.reg a, .reg b]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false) (ha : (a, .bits 32 x) ∈ F)
    (hb : (b, .bits 32 y) ∈ F)
    (hwrite : ∀ R, Holds R F → Holds (Function.update R dst (some (.bits 32
      (truncBits 32 (truncBits 32 x + truncBits 32 y))))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  apply scalarStepU hc rfl rfl hs
  · intro t u hF he
    have h1 := holds_mem hF ha
    have h2 := holds_mem hF hb
    have hx : readBits L g t 32 (.reg a) = .ok (truncBits 32 x) := by
      simp [readBits, readReg, h1]; rfl
    have hy : readBits L g t 32 (.reg b) = .ok (truncBits 32 y) := by
      simp [readBits, readReg, h2]; rfl
    have vx : readValue L g t 32 (.reg a) = .ok (.bits 32 x) := by
      simp [readValue, readReg, h1]; rfl
    have vy : readValue L g t 32 (.reg b) = .ok (.bits 32 y) := by
      simp [readValue, readReg, h2]; rfl
    simp only [execInt, DType.width, bind, Except.bind, pure, Except.pure, vx, vy, hx, hy] at he
    exact (Except.ok.inj he).symm
  · exact hwrite

/-- An `add.s32` of a register that holds a 32-bit word and an immediate. -/
theorem addImmStep {x : BitVec 64} {k : Int}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 32, false, [some dst],
      [.reg a, .imm k]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false) (ha : (a, .bits 32 x) ∈ F)
    (hwrite : ∀ R, Holds R F → Holds (Function.update R dst (some (.bits 32
      (truncBits 32 (truncBits 32 x + truncBits 32 (BitVec.ofInt 64 k)))))) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  apply scalarStepU hc rfl rfl hs
  · intro t u hF he
    have h1 := holds_mem hF ha
    have hx : readBits L g t 32 (.reg a) = .ok (truncBits 32 x) := by
      simp [readBits, readReg, h1]; rfl
    have vx : readValue L g t 32 (.reg a) = .ok (.bits 32 x) := by
      simp [readValue, readReg, h1]; rfl
    have himm : readBits L g t 32 (.imm k) = .ok (truncBits 32 (BitVec.ofInt 64 k)) := rfl
    have vimm : readValue L g t 32 (.imm k) =
        .ok (.bits 32 (truncBits 32 (BitVec.ofInt 64 k))) := rfl
    simp only [execInt, DType.width, bind, Except.bind, pure, Except.pure, vx, hx, himm, vimm]
      at he
    exact (Except.ok.inj he).symm
  · exact hwrite

end PTX.Kernels.InklingRelDecode.Proof.Lib
