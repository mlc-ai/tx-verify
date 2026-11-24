-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Instr

@[expose] public section

/-! # The positions of an instruction class, by one pass over the code

`scan f 0 code` lists the positions whose instruction is in class `f`. A check that no position of
a list is in the class compares two lists of positions; looking each position up in the code
(`code[pc]?`) instead walks the code once per position. -/

namespace PTX.Flow
open PTX

/-- The positions from `i` on whose instruction is in class `f`. -/
def scan (f : Op → Bool) : Nat → List Instr → List Nat
  | _, [] => []
  | i, ins :: rest => if f ins.op then i :: scan f (i + 1) rest else scan f (i + 1) rest

theorem mem_scan {f : Op → Bool} {code : List Instr} {pc : Nat} {ins : Instr}
    (h : code[pc]? = some ins) (hf : f ins.op = true) (i : Nat) : i + pc ∈ scan f i code := by
  induction code generalizing pc i with
  | nil => simp at h
  | cons a rest ih =>
    cases pc with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [scan, hf]
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h (i + 1)
      rw [show i + (n + 1) = i + 1 + n by omega]
      simp only [scan]
      split
      · exact List.mem_cons_of_mem _ this
      · exact this

end PTX.Flow
