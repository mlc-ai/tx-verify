-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Bound.Ranks

@[expose] public section

/-! # A consumer's work per task

Every counted consumer event lowers its rank, except a successful poll at its response wait
(`r`), which starts the next task and raises the rank by less than `resetBudget`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Bound

open PTX PTX.Flow

/-- A consumer event lowers the consumer's rank, except a successful poll at its response wait. -/
theorem cons_step {L : Launch} {g : Nat} {d d' : Consumer.D} {e : Event} {r : Bool}
    (hn : Consumer.next L g d e = some (some d'))
    (hr : d.site = .clcWait → e.counts = true → r = true) :
    consRank d' + (if e.counts then 1 else 0) ≤ consRank d + (if r then resetBudget else 0) := by
  obtain ⟨site, m, n, m', n', cp, ap, rs, x, acc, base⟩ := d
  simp only at hr
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  have hz : 0 ≤ (if r then resetBudget else 0) := Nat.zero_le _
  cases site with
  | clcWait =>
    simp only [Consumer.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hok := counts_of_wait hk
      cases ok
      · simp [consRank, hok]
      · simp [consRank, hok, hr rfl hok, resetBudget]
    · cases hn
  | accWait =>
    simp only [Consumer.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      simp only [Option.some.injEq] at hn
      subst hn
      rw [counts_of_wait hk]
      cases ok <;> simp [consRank]
    · cases hn
  | load j =>
    simp only [Consumer.next] at hn
    have := j.isLt
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      simp only [consRank]
      omega
    · cases hn
  | store k i el =>
    simp only [Consumer.next] at hn
    have := k.isLt
    have := i.isLt
    have := el.isLt
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      simp only [consRank] <;> omega
  | clcLoad =>
    simp only [Consumer.next] at hn
    split at hn
    · simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨_, -, rfl⟩ := hn
      simp only [consRank]
      omega
    · cases hn
  | clcStatus | clcFirst =>
    simp only [Consumer.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      (try split_ifs) <;> simp only [consRank] <;> omega
    · cases hn
  | ldBase =>
    simp only [Consumer.next] at hn
    repeat' (first | split at hn)
    all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
    all_goals (try subst hn)
    all_goals (try simp only [consRank])
    all_goals omega
  | exit => simp [Consumer.next] at hn
  | _ =>
    simp only [Consumer.next] at hn
    repeat' (first | split_ifs at hn)
    all_goals (simp only [Option.some.injEq] at hn)
    all_goals (subst hn)
    all_goals (simp only [consRank])
    all_goals omega

end PTX.Kernels.Fp16Gemm8192.Proof.Bound
