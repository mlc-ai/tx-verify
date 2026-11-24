-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Vote

@[expose] public section

/-! # Votes with a given member mask

A proof tool for ghost ledgers that count warp votes (`Code.counted`): `voteWith m e` holds of a
ballot or mode vote whose member mask is `m`. Its value on a vote event is stated by a lemma for
any mask (`voteWith_vote`, `voteWith_voteMode`), so a kernel never evaluates it on a literal
mask such as `2 ^ 32 - 1` (a kernel evaluation that timed out on the tml-fa4 MMA warp); on any
other event kind it is false (`voteWith_of_none`). -/

namespace PTX.Flow
open PTX

/-- A ballot or mode vote whose member mask is `m`. -/
def voteWith (m : Nat) (e : Event) : Bool := (voteClass e.kind).any (·.mask == m)

@[simp] theorem voteWith_vote (m pc : Nat) (a : Bool) (b : BitVec 32) :
    voteWith m ⟨pc, .vote m a b⟩ = true := by
  simp [voteWith, voteClass]

@[simp] theorem voteWith_voteMode (m pc : Nat) (q : VoteMode) (a d : Bool) :
    voteWith m ⟨pc, .voteMode q m a d⟩ = true := by
  simp [voteWith, voteClass]

/-- A vote with another mask is not counted. -/
theorem voteWith_vote_ne {m m' pc : Nat} {a : Bool} {b : BitVec 32} (h : m' ≠ m) :
    voteWith m ⟨pc, .vote m' a b⟩ = false := by
  simp [voteWith, voteClass, h]

/-- An event that is no vote is not counted. -/
theorem voteWith_of_none {m : Nat} {e : Event} (h : voteClass e.kind = none) :
    voteWith m e = false := by
  simp [voteWith, h]

end PTX.Flow
