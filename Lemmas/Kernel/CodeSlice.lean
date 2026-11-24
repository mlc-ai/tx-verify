-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace PTX

/-- Read one instruction using a certified slice of the program. -/
theorem codeLookupOfSlice {α : Type} {code part : List α} {start size offset : Nat}
    {ins : α} (hs : (code.drop start).take size = part) (ho : offset < size)
    (hi : part[offset]? = some ins) : code[start + offset]? = some ins := by
  rw [← List.getElem?_drop, ← List.getElem?_take_of_lt ho, hs]
  exact hi

end PTX
