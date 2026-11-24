-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Startup.Machine

@[expose] public section

/-! # The startup's events are bounded (G1)

Every transition of the startup machine goes to a site at a larger program counter
(`succ_pc_lt`): the shuffles, the elections and initializations in code order, the fence, the
barrier, and the dispatch to a role's first instruction. So the startup's site position is a
measure that increases at every event, and it is below 9206 (`Site.pc_le`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Startup
open PTX PTX.Flow

theorem nonzero_pc : ∀ j, electPc j < (nonzeroSite j).pc := by decide
theorem after_pc : ∀ j, electPc j < (afterSite j).pc := by decide
theorem firstInit_pc : ∀ j, electPc j < (firstInit j).pc := by decide
theorem initSucc_elect : ∀ n j, initSucc n = .elect j →
    initPc n < (nonzeroSite j).pc ∧ initPc n < (afterSite j).pc := by decide
theorem initSucc_pc : ∀ n, (∀ j, initSucc n ≠ .elect j) → initPc n < (initSucc n).pc := by
  decide
theorem enter_pc (r : Entry) : 173 < (Site.enter r).pc := by cases r <;> decide

theorem afterBlock_gt {x : Nat} (d : D) (j : Fin 16)
    (h : x < (nonzeroSite j).pc ∧ x < (afterSite j).pc) : x < (afterBlock d j).site.pc := by
  unfold afterBlock
  split
  · exact h.1
  · exact h.2

theorem afterBlock_pc (d : D) (j : Fin 16) : electPc j < (afterBlock d j).site.pc :=
  afterBlock_gt d j ⟨nonzero_pc j, after_pc j⟩

theorem enterOf_pc (d : D) : 173 < (enterOf d).site.pc := by
  unfold enterOf
  repeat' split
  all_goals exact enter_pc _

/-- Every site is at a program counter below 9206. -/
theorem Site.pc_le (s : Site) : s.pc ≤ 9205 := by
  cases s with
  | sh j => revert j; decide
  | elect j => revert j; decide
  | init n => revert n; decide
  | fence | bar => decide
  | enter r => cases r <;> decide

/-- Every site is at a program counter of at least 25 (the first shuffle). -/
theorem Site.pc_ge (s : Site) : 25 ≤ s.pc := by
  cases s with
  | sh j => revert j; decide
  | elect j => revert j; decide
  | init n => revert n; decide
  | fence | bar => decide
  | enter r => cases r <;> decide

/-- **Every transition of the startup increases the program counter.** -/
theorem succ_pc_lt {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : succ L g d e = some (some d')) : d.site.pc < d'.site.pc := by
  obtain ⟨s, x1, x2, x3⟩ := d
  cases s with
  | sh j =>
    simp only [succ] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        fin_cases j
        · show 25 < 34; decide
        · show 34 < 35; decide
        · simp only [Fin.reduceFinMk, Fin.isValue]
          split
          · show 35 < 172; decide
          · show 35 < 46; decide
      · cases h
    · cases h
  | elect j =>
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split
      · exact firstInit_pc j
      · exact afterBlock_pc _ j
    · cases h
  | init n =>
    simp only [succ] at h
    split at h
    · rename_i j hj
      simp only [Option.some.injEq] at h
      subst h
      exact afterBlock_gt _ j (initSucc_elect n j hj)
    · rename_i s hs
      simp only [Option.some.injEq] at h
      subst h
      exact initSucc_pc n hs
  | fence => simp only [succ, Option.some.injEq] at h; subst h; show 172 < 173; decide
  | bar => simp only [succ, Option.some.injEq] at h; subst h; exact enterOf_pc _
  | enter r => simp [succ] at h

/-- The startup's measure: the site's position after the first shuffle's (0 at the first state,
at most 9180). -/
def measure (d : D) : Nat := d.site.pc - 25

theorem measure_init : measure ⟨.sh 0, 0, 0, 0⟩ = 0 := rfl

theorem measure_le (d : D) : measure d ≤ 9180 := by
  have := Site.pc_le d.site; unfold measure; omega

/-- **The startup's measure increases at every transition** (`Frame.counts_le_of_measure`'s step
premise for this fragment). -/
theorem measure_lt {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : succ L g d e = some (some d')) : measure d < measure d' := by
  have := succ_pc_lt h; have := Site.pc_ge d.site; unfold measure; omega

end PTX.Kernels.TmlFa4Fwd.Proof.Startup
