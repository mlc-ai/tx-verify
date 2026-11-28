-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRules

@[expose] public section

/-! # The pack of two halves into a 32-bit register

`mov.b32 d, {a, b}` as an item of a generated run: Core's move joins two 16-bit halves. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- `mov.b32 d, {a, b}`. -/
def pack32Op (d : Nat) (s : List Nat) : Op :=
  .move ⟨.pack, .int .b 32, [some d], [.reg (s.getD 0 0), .reg (s.getD 1 0)]⟩

/-- The outcome: the join of two halves of two bytes. -/
def pack32E : List Value → Exec Value
  | [x, y] => if x.bytes = 2 ∧ y.bytes = 2 then .ok (joinValue x y) else .error .typeMismatch
  | _ => .error .noRule

theorem rule_pack32 {d a b : Nat} (pc : Nat) (hp : intPc pc = true) :
    ∀ t : TState, t.pc = pc →
      (XItem.fn (pack32Op d [a, b]) d [a, b] pack32E).Rule Assumptions.all L g t := by
  intro t ht W hW
  have ha := hW a (by simp)
  have hb := hW b (by simp)
  have hR := noRuleSm (L := L) (g := g) (op := pack32Op d [a, b]) pc hp rfl t ht
  simp only [pack32Op, List.getD_cons_zero, List.getD_cons_succ] at hR
  show execLocalA Assumptions.all L g t (pack32Op d [a, b]) = _
  simp only [(smSegFree hp).exec ht, execLocalRule_of_none hR, pack32Op, execLocal, Op.rule,
    MoveInstr.rule, execMove, readValue, pack32E, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ]
  by_cases h : (W a).bytes = 2 ∧ (W b).bytes = 2 <;>
    simp [h, Except.map, readReg, ha, hb, DType.width, bind, Except.bind, pure, Except.pure, throw,
      throwThe, MonadExceptOf.throw]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
