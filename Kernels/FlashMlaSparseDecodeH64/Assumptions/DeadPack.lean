-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
open PTX

noncomputable section

/-- The only packed moves with an unwritten high half in the frozen instruction stream.
Each is followed by an unpack into the low destination and the discard sink. -/
def deadPackWords : Nat → Option (Nat × Nat × Nat)
  | 208 => some (3144, 467, 950)
  | 712 => some (3565, 2951, 1715)
  | _ => none

/-- Use a representative for the unwritten half while preserving the live low half. -/
def deadPackRule (L : Launch) (g : Nat) (t : TState) (op : Op) : Option (Exec TState) :=
  match op with
  | .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩ =>
    if deadPackWords t.pc = some (d, a, b) then
      some (do
        let v ← readValue L g t 32 (.reg a)
        unless v.bytes = 4 do throw .typeMismatch
        pure (next (setReg t d (joinValue v (.bits 32 0)))))
    else none
  | _ => none

/-- The rule declines every instruction at an unselected location. -/
theorem deadPackRule_of_none {L : Launch} {g : Nat} {t : TState} {op : Op}
    (h : deadPackWords t.pc = none) : deadPackRule L g t op = none := by
  unfold deadPackRule
  split <;> simp [h]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
