-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierRoundHistory
public import Lemmas.CtaBarrier.CtaBarrierTraceHistory

@[expose] public section

section
namespace PTX.CtaBarrier
variable {α : Type}

/-- A resource update settles completion immediately within this abstract object. -/
theorem complete_settle (block : Nat) (exited : Finset Nat) (s : Slot) :
    complete block exited (settle block exited s) = false := by
  unfold settle
  split_ifs with hc
  · simp [complete]
  · cases h : complete block exited s <;> simp_all

/-- Every checked prefix ends with its completed resource phases settled. -/
theorem FullRounds.pending {block rounds : Nat} {h : List (Record α)} {s : State}
    (hp : FullRounds rounds h) (hr : run block {} h = .ok s) :
    complete block s.exited (s.slots 0) = false := by
  induction h using List.reverseRecOn generalizing s with
  | nil => cases hr; rfl
  | @append_singleton xs r ih =>
    obtain ⟨u,hu⟩ := run_prefix hr
    have hf : r.perform block u = .ok s := by
      rw [run_append,hu] at hr
      cases hh : r.perform block u with
      | error err => simp [run,hh,Except.bind] at hr
      | ok v => simpa only [run,hh,Except.bind,Except.ok.injEq] using hr
    have hh := hp xs r [] (by simp)
    cases r with
    | arrival id warp count lanes =>
      obtain ⟨rfl,rfl,_⟩ := hh
      simp only [Record.perform] at hf
      split_ifs at hf
      obtain ⟨_,_,_,he,ht⟩ := arrive_full_shape hf
      rw [he,ht]
      exact complete_settle _ _ _
    | exit g e =>
      obtain ⟨_,_,he,ht⟩ := exit_shape hf
      rw [he,ht]
      exact complete_settle _ _ _

end PTX.CtaBarrier
end

section
namespace PTX.CtaBarrier
variable {α : Type}

/-- All valid lanes of a warp, with source references supplied by a client. -/
def fullLanes (block warp : Nat) (event : Nat → α) : List (Nat × α) :=
  ((List.range 32).filter (fun lane => decide (warp*32+lane < block))).map
    (fun lane => (warp*32+lane,event (warp*32+lane)))

end PTX.CtaBarrier
end
