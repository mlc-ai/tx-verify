-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Bound.Ranks

@[expose] public section

/-! # The scheduler's work per task

Every counted scheduler event lowers its rank, except a successful poll at its response wait
(`r`), which starts the next request and raises the rank by less than `resetBudget`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Bound

open PTX PTX.Flow

/-- A scheduler event lowers the scheduler's rank, except a successful poll at its response
wait. -/
theorem sched_step {L : Launch} {g : Nat} {d d' : Scheduler.D} {e : Event} {r : Bool}
    (hn : Scheduler.next L g d e = some (some d'))
    (hr : d.site = .clcWait → e.counts = true → r = true) :
    schedRank d' + (if e.counts then 1 else 0) ≤ schedRank d + (if r then resetBudget else 0) := by
  obtain ⟨site, ap, cp, rs, x⟩ := d
  simp only at hr
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  have hz : 0 ≤ (if r then resetBudget else 0) := Nat.zero_le _
  cases site with
  | ackWait =>
    simp only [Scheduler.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      rw [counts_of_wait hk]
      cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;>
        subst hn <;> simp [schedRank]
    · cases hn
  | clcWait =>
    simp only [Scheduler.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      have hok := counts_of_wait hk
      cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn <;>
        subst hn
      · simp [schedRank, hok]
      · simp [schedRank, hok, hr rfl hok, resetBudget]
    · cases hn
  | elect =>
    simp only [Scheduler.next] at hn
    split at hn
    · split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
      all_goals (try simp only [Scheduler.loopHead])
      all_goals (try split_ifs)
      all_goals simp only [schedRank]
      all_goals omega
    · cases hn
  | ack =>
    simp only [Scheduler.next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
    all_goals (try simp only [Scheduler.loopHead])
    all_goals (try split_ifs)
    all_goals simp only [schedRank]
    all_goals omega
  | clcLoad =>
    simp only [Scheduler.next] at hn
    split at hn
    · simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨_, -, rfl⟩ := hn
      simp only [schedRank]
      omega
    · cases hn
  | clcStatus =>
    simp only [Scheduler.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      (try split_ifs) <;> simp only [schedRank] <;> omega
    · cases hn
  | clcFirst =>
    simp only [Scheduler.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      simp only [schedRank]
      omega
    · cases hn
  | tryCancel | arriveTx | clcFence | exitArrive | exitWait =>
    simp only [Scheduler.next, Option.some.injEq] at hn
    subst hn
    simp only [schedRank]
    omega
  | exit => simp [Scheduler.next] at hn

end PTX.Kernels.Fp16Gemm8192.Proof.Bound
