-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Events
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # The member mask of a ballot

A proof tool. A `vote.sync.ballot` fires its event only with the full member mask (the template
rejects any other), so every ballot event names the full warp (`fires_vote_mask`). -/

namespace PTX.Flow
open PTX PTX.Proof

/-- **A ballot event has the full member mask.** -/
theorem fires_vote_mask {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} {d a : Nat} {neg : Bool} {mask : Opnd} {m : Nat} {p : Bool}
    {b : BitVec 32} {ty : Option DType}
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.vote .ballot neg, ty, [some d], [.reg a], some mask⟩)) e o)
    (hk : e.kind = .vote m p b) : m = 2 ^ 32 - 1 := by
  simp only [eventTmpl, warpTmpl_vote, voteTmpl] at hf
  split at hf
  · split_ifs at hf with hm
    · simp only [Fires] at hf
      obtain ⟨b', he, -⟩ := hf
      rw [he] at hk
      injection hk with h1
      rw [← h1]; exact hm.1
    · simp only [Fires] at hf
      rw [hf.1] at hk
      cases hk
  all_goals simp only [Fires] at hf
  all_goals rw [hf.1] at hk
  all_goals cases hk

end PTX.Flow
