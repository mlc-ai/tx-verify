-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesP
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Machine

@[expose] public section

/-! # The moves of the bias words as items of a run

`mov.u16 d, s` (the defaults of the loads' registers), `mov.b16 d, 0` and the pack of two halves
(`GenRulesP`): Core's move, read as the outcome function of an item of a run. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- `mov.u16 d, s`. -/
def mv16Op (d s : Nat) : Op := .move ⟨.scalar, .int .u 16, [some d], [.reg s]⟩
/-- `mov.b16 d, 0`. -/
def mi16Op (d : Nat) : Op := .move ⟨.scalar, .int .b 16, [some d], [.imm 0]⟩

/-- The outcome of a 16-bit move: the word itself. -/
def mv16E : List Value → Exec Value
  | [x] => if x.bytes = 2 then .ok x else .error .typeMismatch
  | _ => .error .noRule

theorem rule_mv16 {d s : Nat} (pc : Nat) (hp : intPc pc = true) :
    ∀ t : TState, t.pc = pc → (XItem.fn (mv16Op d s) d [s] mv16E).Rule Assumptions.all L g t := by
  intro t ht W hW
  have hs := hW s (by simp)
  have hR := noRuleSm (L := L) (g := g) (op := mv16Op d s) pc hp rfl t ht
  simp only [mv16Op] at hR
  show execLocalA Assumptions.all L g t (mv16Op d s) = _
  simp only [(smSegFree hp).exec ht, execLocalRule_of_none hR, mv16Op, execLocal, Op.rule,
    MoveInstr.rule, execMove, readValue, mv16E, List.map_cons, List.map_nil]
  by_cases h : (W s).bytes = 2 <;>
    simp [h, Except.map, DType.width, readReg, hs, bind, Except.bind, pure, Except.pure, throw,
      throwThe, MonadExceptOf.throw]

theorem rule_mi16 {d : Nat} (pc : Nat) (hp : intPc pc = true) :
    ∀ t : TState, t.pc = pc →
      (XItem.fn (mi16Op d) d [] fun _ => .ok dflt).Rule Assumptions.all L g t := by
  intro t ht W hW
  have hR := noRuleSm (L := L) (g := g) (op := mi16Op d) pc hp rfl t ht
  simp only [mi16Op] at hR
  show execLocalA Assumptions.all L g t (mi16Op d) = _
  simp only [(smSegFree hp).exec ht, execLocalRule_of_none hR, mi16Op, execLocal, Op.rule,
    MoveInstr.rule, execMove, readValue]
  simp [Except.map, dflt, readBits, truncBits, DType.width, pure, Except.pure, Value.bytes, bind,
    Except.bind]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
