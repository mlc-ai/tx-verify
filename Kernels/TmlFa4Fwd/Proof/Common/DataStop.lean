-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.DataState
public import Lemmas.Kernel.NoUbFirstStop

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow

variable {p : Params} {L : Launch} {g : Nat} {e : Event}

/-- Dispatch and counting preserve which arm of a first stop was taken. -/
theorem data_role_stop {i : Role} {d : (fragD p L g i).D} {n : Cls → Nat}
    (h : (threadD p L g).next (.inr ⟨i,d⟩,n) e = none ∨
      (threadD p L g).next (.inr ⟨i,d⟩,n) e = some none) :
    (fragD p L g i).next d e = none ∨ (fragD p L g i).next d e = some none := by
  change Option.map _ (Option.map _ _) = none ∨ Option.map _ (Option.map _ _) = some none at h
  rcases hn : (fragD p L g i).next d e with _ | _ | b
  · exact .inl rfl
  · exact .inr rfl
  · simp [hn] at h

theorem data_start_stop {s : Startup.D} {n : Cls → Nat}
    (h : (threadD p L g).next (.inl s,n) e = none ∨ (threadD p L g).next (.inl s,n) e = some none) :
    (thread p L g).next (.inl s,n) e = none ∨ (thread p L g).next (.inl s,n) e = some none := by
  change Option.map _ (Option.map _ _) = none ∨ Option.map _ (Option.map _ _) = some none at h ⊢
  rcases hn : Startup.succ L g s e with _ | _ | b
  all_goals simp [hn] at h ⊢

end PTX.Kernels.TmlFa4Fwd.Proof
