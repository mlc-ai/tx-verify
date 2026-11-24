-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorAddress
public import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace PTX.TensorAddress

theorem lookup_some_iff {rank : Nat} (d : Geometry rank) (coord : Fin rank → Int)
    (byte addr : Nat) :
    lookup d coord byte = some addr ↔
      InBounds d coord ∧ byte < d.elementBytes ∧ addr = byteAddress d coord byte := by
  simp only [lookup, InBounds]
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro heq; exact ⟨h.1, h.2, heq.symm⟩
    · rintro ⟨_, _, heq⟩; exact heq.symm
  · constructor
    · intro heq; cases heq
    · rintro ⟨hcoord, hbyte, _⟩
      exact False.elim (h ⟨hcoord, hbyte⟩)

end PTX.TensorAddress
