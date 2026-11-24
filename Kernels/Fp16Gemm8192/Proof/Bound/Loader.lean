-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Bound.Ranks

@[expose] public section

/-! # The loader's work per task

Every counted loader event lowers the loader's rank, except a successful poll at its response
wait (`r`), which starts the next task and raises the rank by less than `resetBudget`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Bound

open PTX PTX.Flow

/-- A loader event lowers the loader's rank, except a successful poll at its response wait. -/
theorem loader_step {L : Launch} {g : Nat} {l l' : Loader.D} {e : Event} {r : Bool}
    (hi : Loader.Inv l) (hn : Loader.next L g l e = some (some l'))
    (hr : l.site = .clcWait → e.counts = true → r = true) :
    loaderRank l' + (if e.counts then 1 else 0) ≤ loaderRank l + (if r then resetBudget else 0) :=
      by
  obtain ⟨site, m, n, q, cp, rs, x⟩ := l
  have hq := hi.q
  have hq8 := hi.q8
  simp only at hq hq8 hr
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  have hz : 0 ≤ (if r then resetBudget else 0) := Nat.zero_le _
  cases site with
  | wait b =>
    simp only [Loader.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      simp only [Option.some.injEq] at hn
      subst hn
      rw [counts_of_wait hk]
      cases ok
      · simp [loaderRank]
      · simp [loaderRank]
        omega
    · cases hn
  | load b j =>
    simp only [Loader.next] at hn
    have := b.isLt
    have := j.isLt
    split_ifs at hn with h1 h2 h3 <;> simp only [Option.some.injEq] at hn <;> subst hn
    all_goals (try (unfold Loader.endOfTrip; split_ifs))
    all_goals (simp only [loaderRank]; (try split_ifs) <;> (try dsimp only at *) <;> omega)
  | arrive b =>
    simp only [Loader.next] at hn
    have := b.isLt
    split_ifs at hn with h1 <;> simp only [Option.some.injEq] at hn <;> subst hn
    all_goals (try (unfold Loader.endOfTrip; split_ifs))
    all_goals (simp only [loaderRank]; (try split_ifs) <;> (try dsimp only at *) <;> omega)
  | clcWait =>
    simp only [Loader.next] at hn
    split at hn
    · rename_i _ _ ok _ _ hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hok := counts_of_wait hk
      cases ok
      · simp [loaderRank, hok]
      · simp [loaderRank, hok, hr rfl hok, resetBudget]
    · cases hn
  | drain i =>
    simp only [Loader.next] at hn
    have := i.isLt
    split at hn
    · rename_i _ _ ok _ _ hk
      rw [counts_of_wait hk]
      cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
      · subst hn
        simp [loaderRank]
      · split_ifs at hn with h1 <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
          simp only [loaderRank] <;> split_ifs <;> omega
    · cases hn
  | ack =>
    simp only [Loader.next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      simp only [loaderRank] <;> split_ifs <;> omega
  | clcLoad =>
    simp only [Loader.next] at hn
    split at hn
    · simp only [Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨_, -, rfl⟩ := hn
      simp only [loaderRank]
      split_ifs <;> omega
    · cases hn
  | clcStatus =>
    simp only [Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      (try split_ifs) <;> simp only [loaderRank] <;> omega
    · cases hn
  | clcFirst =>
    simp only [Loader.next] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      simp only [loaderRank]
      split_ifs <;> omega
    · cases hn
  | clcFence =>
    simp only [Loader.next, Option.some.injEq] at hn
    subst hn
    simp only [loaderRank]
    split_ifs <;> omega
  | exitArrive =>
    simp only [Loader.next, Option.some.injEq] at hn
    subst hn
    simp only [loaderRank]
    split_ifs <;> omega
  | exitWait =>
    simp only [Loader.next, Option.some.injEq] at hn
    subst hn
    simp only [loaderRank]
    split_ifs <;> omega
  | exit => simp [Loader.next] at hn

end PTX.Kernels.Fp16Gemm8192.Proof.Bound
