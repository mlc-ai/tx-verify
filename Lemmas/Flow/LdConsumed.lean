-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.TcLdDataflow

@[expose] public section

/-! # `ldConsumedAt` on a slice of the code

A proof tool. `ldConsumedAt K pc` (the condition of a `tcLdDataflowAt` assumption at a load) reads
`K.code[pc]?` and scans `K.code.drop (pc + 1)`: the kernel evaluates both from the head of the code
at every load, which for a load deep in a long kernel costs about a second each. With the code
from position `lo` on given once as a list (`K.code.drop lo = tail`, one evaluation), the same
condition is `ldConsumedIn tail (pc - lo)`, which walks only the slice (`ldConsumedAt_eq_in`). -/

namespace PTX.Flow
open PTX PTX.Assumption

/-- `ldConsumedAt` at position `i` of a list of instructions. -/
def ldConsumedIn (tail : List Instr) (i : Nat) : Bool :=
  match tail[i]? with
  | some ⟨_, .tcLd ds _ _ red⟩ =>
    let ds := ds ++ red.toList.map (·.dst)
    scanConsumed (tail.drop (i + 1)) ds (ds.map fun d => (d, [d]))
  | _ => false

/-- **`ldConsumedAt` from a slice of the code.** -/
theorem ldConsumedAt_eq_in {K : Kernel} {lo pc : Nat} {tail : List Instr}
    (h : K.code.drop lo = tail) (hpc : lo ≤ pc) :
    ldConsumedAt K pc = ldConsumedIn tail (pc - lo) := by
  subst h
  have h1 : K.code[pc]? = (K.code.drop lo)[pc - lo]? := by
    rw [List.getElem?_drop]; congr 1; omega
  have h2 : K.code.drop (pc + 1) = (K.code.drop lo).drop (pc - lo + 1) := by
    rw [List.drop_drop]; congr 1; omega
  unfold ldConsumedAt ldConsumedIn
  rw [h1, h2]
  rfl

end PTX.Flow
