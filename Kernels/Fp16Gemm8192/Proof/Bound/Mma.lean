-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Bound.Ranks

@[expose] public section

/-! # The MMA thread's work per task

Every counted event of an MMA thread lowers its rank, except a successful poll at its response
wait (`r`), which starts the next task and raises the rank by less than `resetBudget`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Bound

open PTX PTX.Flow

/-- An MMA event lowers the MMA thread's rank, except a successful poll at its response wait. -/
theorem mma_step {L : Launch} {g : Nat} {d d' : Mma.D} {e : Event} {r : Bool}
    (hi : Mma.Inv d) (hn : Mma.next L g d e = some (some d'))
    (hr : d.site = .clcWait → e.counts = true → r = true) :
    mmaRank d' + (if e.counts then 1 else 0) ≤ mmaRank d + (if r then resetBudget else 0) := by
  obtain ⟨site, w, q, fp, ap, cp, rs, x⟩ := d
  have hq := hi.q
  have hq4 := hi.q4
  simp only at hq hq4 hr
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  have hz : 0 ≤ (if r then resetBudget else 0) := Nat.zero_le _
  cases site with
  | full s =>
    simp only [Mma.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      simp only [Option.some.injEq] at hn
      subst hn
      rw [counts_of_wait hk]
      cases ok
      · simp [mmaRank]
      · simp [mmaRank]
        omega
    · cases hn
  | accWait =>
    simp only [Mma.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      simp only [Option.some.injEq] at hn
      subst hn
      rw [counts_of_wait hk]
      cases ok
      · simp [mmaRank]
      · simp [mmaRank]
        omega
    · cases hn
  | clcWait =>
    simp only [Mma.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hok := counts_of_wait hk
      cases ok
      · simp [mmaRank, hok]
      · simp [mmaRank, hok, hr rfl hok, resetBudget]
    · cases hn
  | mma s j =>
    simp only [Mma.next] at hn
    have := s.isLt
    have := j.isLt
    split_ifs at hn with h1 <;> simp only [Option.some.injEq] at hn <;> subst hn
    all_goals (simp only [mmaRank]; omega)
  | commit s =>
    simp only [Mma.next] at hn
    have := s.isLt
    split_ifs at hn with h1 <;> simp only [Option.some.injEq] at hn <;> subst hn
    all_goals (try (unfold Mma.endOfTrip; split_ifs))
    all_goals (simp only [mmaRank]; (try dsimp only at *); omega)
  | elect =>
    simp only [Mma.next] at hn
    split at hn
    · split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
        simp only [mmaRank] <;> omega
    · cases hn
  | clcLoad =>
    simp only [Mma.next] at hn
    split at hn
    · simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨_, -, rfl⟩ := hn
      simp only [mmaRank]
      omega
    · cases hn
  | clcStatus =>
    simp only [Mma.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      (try split_ifs) <;> simp only [mmaRank] <;> omega
    · cases hn
  | clcFirst =>
    simp only [Mma.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      simp only [mmaRank]
      omega
    · cases hn
  | accCommit =>
    simp only [Mma.next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      simp only [mmaRank] <;> omega
  | clcFence | ack | exitArrive | exitWait =>
    simp only [Mma.next, Option.some.injEq] at hn
    subst hn
    simp only [mmaRank]
    omega
  | exit => simp [Mma.next] at hn

end PTX.Kernels.Fp16Gemm8192.Proof.Bound
