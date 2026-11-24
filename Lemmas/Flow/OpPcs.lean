-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Instr
public import Core.Data.Types

@[expose] public section

/-! # Where a kind of instruction occurs

A proof tool. Whether every instruction of a kind is at one of the listed positions is decided
once on the code (`OpPcs`); then each such instruction's position is listed (`OpPcs.mem`). -/

namespace PTX.Flow

/-- Every instruction `p` selects is at a position in `l`. -/
def OpPcs (code : List Instr) (p : Op → Bool) (l : List Nat) : Bool :=
  (List.range code.length).all fun pc => match code[pc]? with
    | some ins => !p ins.op || l.contains pc
    | none => true

theorem OpPcs.mem {code : List Instr} {p : Op → Bool} {l : List Nat} (h : OpPcs code p l = true)
    {pc : Nat} {ins : Instr} (hc : code[pc]? = some ins) (hp : p ins.op = true) : pc ∈ l := by
  have hlt : pc < code.length := by
    rcases Nat.lt_or_ge pc code.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hc; cases hc
  have h' := List.all_eq_true.mp h pc (List.mem_range.mpr hlt)
  rw [hc] at h'
  simp only [hp, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h'
  exact h'

end PTX.Flow
