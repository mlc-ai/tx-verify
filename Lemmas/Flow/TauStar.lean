-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run

@[expose] public section

/-! # Zero or more local steps of a thread

`TauStar K A L g t t'`: the thread `g` moves from `t` to `t'` by local steps only (no event). -/

namespace PTX

/-- Zero or more local steps. -/
abbrev TauStar (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (t t' : TState) : Prop :=
  Relation.ReflTransGen (Tau K A L g) t t'

end PTX
