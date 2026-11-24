-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Places

/-! # Counts as closed forms in passed places

A loop body with points 10 (inside the round) and 20 (after it): a state is a program counter,
`before s q` holds for the points below `s` (a round's points only inside the round). The move
from 10 to 15 adds point 10 to the count of the class `[10, 20]`; the end of the round from 15
back to 5 adds one round and restarts the round's points. -/

namespace PTX.Tests.Places
open PTX.Flow.Places

def inR (q : Nat) : Bool := decide (q < 16)
def bef (s q : Nat) : Bool := decide (q < s)

example (r : Nat) : passed bef inR [10, 20] 15 r = passed bef inR [10, 20] 10 r + 1 := by
  have h := passed_move (before := bef) (inRound := inR) (pc := id) (pts := [10, 20])
    (fun s => by simp [bef]) (by decide) (s := 10) (s' := 15) (by decide) r
  simpa using h

example (r : Nat) : passed bef inR [10] 0 (r + 1) = passed bef inR [10] 15 r + 0 := by
  have h := passed_rmove (before := bef) (inRound := inR) (pc := id) (pts := [10])
    (fun s => by simp [bef]) (by decide) (s := 15) (s' := 0) (by decide) (by decide) r
  simpa using h

end PTX.Tests.Places
