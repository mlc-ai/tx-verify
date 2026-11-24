-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

/-! # Two events of one thread with the same count before them

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/SameCount.lean`): two
events of one thread that both satisfy `p` and have the same number of earlier events satisfying `p`
are one event (moved from the first tree's `Proof/Protocol/SxUCopy.lean`, stated for any predicate).
-/

namespace PTX.Flow
open PTX

variable {X : Execution} {g : Nat}

theorem same_count {p : Event → Bool} {k1 k2 : Nat} {e1 e2 : Event}
    (h1 : X.get (g, k1) = some e1) (h2 : X.get (g, k2) = some e2) (hi1 : p e1 = true)
    (hi2 : p e2 = true)
    (hc : ((X.tr g).take k1).countP p = ((X.tr g).take k2).countP p) : k1 = k2 := by
  have key : ∀ {a b : Nat} {ea : Event}, X.get (g, a) = some ea → p ea = true → a < b →
      ((X.tr g).take a).countP p < ((X.tr g).take b).countP p := by
    intro a b ea ha hia hab
    have hs : ((X.tr g).take (a + 1)).countP p = ((X.tr g).take a).countP p + 1 := by
      have ht : (X.tr g).take (a + 1) = (X.tr g).take a ++ [ea] := by
        rw [List.take_add_one, show (X.tr g)[a]? = some ea from ha, Option.toList_some]
      rw [ht, List.countP_append, List.countP_singleton, hia]
      rfl
    have hle : ((X.tr g).take (a + 1)).countP p ≤ ((X.tr g).take b).countP p :=
      (List.take_sublist_take_left (show a + 1 ≤ b by omega)).countP_le
    omega
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := key h1 hi1 h
    omega
  · exact h
  · have := key h2 hi2 h
    omega

end PTX.Flow
