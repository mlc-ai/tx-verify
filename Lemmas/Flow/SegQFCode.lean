-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQF

@[expose] public section

/-! # The instructions of a run from the per-pc code lemmas

A generated run takes its instruction list from the lemmas `code_<pc>` instead of evaluating
`code.drop a`: `takeCode` adds one instruction to the front, `takeNil` ends the list. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow

theorem takeNil (c : List Instr) (a : Nat) : (c.drop a).take 0 = [] := rfl

theorem takeCode {c : List Instr} {a n : Nat} {i : Instr} {l : List Instr}
    (h : c[a]? = some i) (hl : (c.drop (a + 1)).take n = l) : (c.drop a).take (n + 1) = i :: l := by
  have : c.drop a = i :: c.drop (a + 1) := by
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp h).1]
    simp [List.getElem?_eq_some_iff.mp h |>.2]
  rw [this, List.take_succ_cons, hl]

theorem checkW_ops {abs : EnvF → Op → Option (List (Nat × TagF))} {qt : Nat → EnvF} {a b : Nat}
    {ops ops' : List Instr} {W : List Nat} (hops : ops' = ops)
    (h : checkW abs qt a b ops W = true) : checkW abs qt a b ops' W = true := hops ▸ h

end PTX.Flow.TyG
