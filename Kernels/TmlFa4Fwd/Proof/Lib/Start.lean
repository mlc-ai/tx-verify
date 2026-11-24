-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape

@[expose] public section

/-! # What the startup fires

The startup machine's sites fire the register moves, the elections, the fences, the barriers and
the lane's entry, and nothing else: no read, no write, no tensor or cluster operation. Each role's
"good" facts need that a startup event is not the kind of event their fact is about. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- **A startup site does not write**: a startup event is neither a write nor a read-modify-write,
whatever bytes it would write. -/
theorem start_no_wr {s : Startup.D} {n : Cls → Nat} {w : Nat} {f : Event}
    (hE : Startup.Ev L g s f) (hS : StartAt L w s n) {dst : Acc} {bytes : List Byte}
    (hk : f.kind = .wr dst bytes ∨ ∃ old, f.kind = .rmw dst old (some bytes)) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := f
  cases site
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hE <;> obtain ⟨_, _, rfl⟩ := hE <;>
      (rcases hk with h | ⟨_, h⟩ <;> cases h)
  case fence | bar =>
    simp only [Startup.Ev] at hE
    subst hE
    rcases hk with h | ⟨_, h⟩ <;> cases h
  all_goals simp only [StartAt] at hS

/-- **A startup site does not issue a tensor copy**: a startup event is no tensor issue. -/
theorem start_no_tensor {s : Startup.D} {h pc a : Nat} {sp : TensorCopy.Spec}
    (hev : Startup.Ev L h s ⟨pc, .tensorIssue a sp⟩) (hx : exit L h s = none) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | enter r => exact absurd hx (by simp [exit])
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
  | fence | bar => simp only [Startup.Ev] at hev; cases hev
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk

end PTX.Kernels.TmlFa4Fwd.Proof
