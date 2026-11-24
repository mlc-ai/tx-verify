-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterStage

@[expose] public section

/-! # An open thread ranks below a pending paired request

A paired Tensor Memory request and a register request rank above every thread
(`exitBase + 20`, `Descent.lean`), so an open obligation of a thread (outside the exit stage, or
in it at an offset of at most 10) is of smaller rank. A pending request passes to the thread that
issued it. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX Classical

noncomputable section

variable {L : Launch} {X : Execution}

/-- The offsets of the exit stage are at most 10. -/
theorem exitOff_le {d : ThreadD} {o : Nat} (h : d.exitOff = some o) : o ≤ 10 := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  · simp [ThreadD.exitOff] at h
  · cases site <;> simp_all [ThreadD.exitOff, Loader.exitOff] <;> omega
  · cases site <;> simp_all [ThreadD.exitOff, Mma.exitOff] <;> omega
  · cases site <;> simp_all [ThreadD.exitOff, Scheduler.exitOff] <;> omega
  · cases site <;> simp_all [ThreadD.exitOff, Consumer.exitOff] <;> omega

/-- A thread's time is at most the exit stage's last offset above `exitBase`. -/
theorem threadTime_le_exitBase {g : Nat} (hg : g < L.threads) :
    threadTime L X g ≤ exitBase L X + 10 := by
  cases hσ : Frame.stateAt (code L) X g (X.tr g).length with
  | none => simp [threadTime, hσ]
  | some σ =>
    cases σ with
    | none => simp [threadTime, hσ]
    | some d =>
      cases hx : d.exitOff with
      | none =>
        have := threadTime_lt_exitBase (X := X) hg hσ hx
        omega
      | some o =>
        rw [threadTime_exit hσ hx]
        have := exitOff_le hx
        omega

/-- An open obligation of a thread ranks below a pending Tensor Memory request. -/
theorem rank_thread_lt_tmem {g : Nat} (hg : g < L.threads) :
    rank L X (.thread g) < rank L X .tmem := by
  have h1 := rank_thread_le (L := L) (X := X) (g := g)
  have h2 := threadTime_le_exitBase (X := X) hg
  simp only [rank] at h1 ⊢
  omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
