-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame

@[expose] public section

/-! # The startup of warps 8 to 15 is no undefined behaviour and does not die

A lane of warps 8 to 15 at a startup state of its reference invariant (`StartAt`) is on the fence
path: the three shuffles, the fence and the CTA barrier, whose shapes have no undefined-behaviour
alternative (`start_safe`), and the startup machine dies only on an event of another kind than its
site's (`start_live`). These are the startup cases of `Frame.noUb_of_followed_live` for every role
of warps 8 to 15. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **No event of a startup state on the fence path is undefined behaviour.** -/
theorem start_safe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {w k : Nat}
    {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hS : StartAt L w s n)
    (f : Fault) : e.kind ≠ .ub f := by
  obtain ⟨hev, -, -⟩ := start_fired hp hX he hσ
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;>
      (obtain ⟨_, _, hk⟩ := hev; rw [hk]; simp)
  | fence => simp only [Startup.Ev] at hev; rw [hev]; simp
  | bar => simp only [Startup.Ev] at hev; rw [hev]; simp
  | _ => simp [StartAt] at hS

/-- **A startup state on the fence path does not die** on the event it fires. -/
theorem start_live (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {w k : Nat}
    {s : Startup.D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (.inl s, n))) (hS : StartAt L w s n)
    (hn : (thread p L g).next (.inl s, n) e = none) : e.kind = .exit := by
  obtain ⟨hev, -, -⟩ := start_fired hp hX he hσ
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  simp only [thread, Code.counted, glued, Code.glue, Option.map_eq_none_iff] at hn
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;>
      (obtain ⟨_, _, hk⟩ := hev; subst hk
       simp [Startup.succ, Startup.word32] at hn; split at hn <;> simp at hn)
  | fence => simp [Startup.succ] at hn
  | bar => simp [Startup.succ] at hn
  | _ => simp [StartAt] at hS

/-- A role state's death as the role machine's: the thread machine dies on a role state exactly
when the role's fragment does. -/
theorem role_next_none {i : Role} {d : (frag p L g i).D} {n : Cls → Nat} {e : Event}
    (hn : (thread p L g).next (.inr ⟨i, d⟩, n) e = none) : (frag p L g i).next d e = none := by
  simp only [thread, Code.counted, glued, Code.glue, Option.map_eq_none_iff] at hn
  exact hn

end
end PTX.Kernels.TmlFa4Fwd.Proof
