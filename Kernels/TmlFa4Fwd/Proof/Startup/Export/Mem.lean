-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Lib.MemKind
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape

@[expose] public section

/-! # The startup accesses no memory -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

theorem start_mem {s : Startup.D} {e : Event} (hev : Startup.Ev L g s e)
    (hx : exit L g s = none) : ¬ MemKind e.kind := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨r, ok, hk⟩ := hev <;>
      subst hk <;> exact id
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> subst hk <;> exact id
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> subst hk <;> exact id
  | fence => simp only [Startup.Ev] at hev; subst hev; exact id
  | bar => simp only [Startup.Ev] at hev; subst hev; exact id
  | enter r => simp [exit] at hx

end PTX.Kernels.TmlFa4Fwd.Proof
