-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Machine

@[expose] public section

/-! # The startup's local time

A startup state is at the pc of its site, two above it (`time`): the code runs forward from the
first shuffle (pc 6) to the CTA barrier (pc 97), so a lane at the barrier is after every lane
before it, and every startup time is at least `2` (the wait-step's lower bound) and below `100`,
under the warpgroups' times (`Common/Time.lean`). The allocation is one below: its address store
(`allocSt`, the same pc) is a later state of lane 0, so a collective's lane is later after it.
An exit state is never a state of the glued machine. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

/-- **The startup's time.** -/
def time (d : D) : Nat :=
  match d.site with
  | .alloc => 92
  | s => s.pc + 2

theorem time_ge (d : D) : 2 ≤ time d := by
  unfold time; split <;> omega

/-- Off the allocation a state is two above its pc. -/
theorem time_of_ne {d : D} (h : d.site ≠ .alloc) : time d = d.site.pc + 2 := by
  unfold time; split <;> simp_all

theorem time_le (d : D) : time d ≤ d.site.pc + 2 := by
  unfold time; split <;> simp_all [Site.pc]

/-- Every site but an exit is at or before the CTA barrier. -/
theorem Site.pc_le (s : Site) (hs : ∀ r, s ≠ .enter r) : s.pc ≤ 97 := by
  cases s with
  | enter r => exact absurd rfl (hs r)
  | init n => fin_cases n <;> decide
  | sh j => fin_cases j <;> decide
  | elect j => fin_cases j <;> decide
  | _ => decide

/-- The only site at pc 97 is the barrier. -/
theorem Site.eq_bar {s : Site} (hs : ∀ r, s ≠ .enter r) (h : s.pc = 97) : s = .bar := by
  cases s with
  | enter r => exact absurd rfl (hs r)
  | init n => revert h; fin_cases n <;> decide
  | sh j => revert h; fin_cases j <;> decide
  | elect j => revert h; fin_cases j <;> decide
  | bar => rfl
  | _ => revert h; decide

/-- Every startup state before its exit is before time `100`. -/
theorem time_lt {d : D} (hx : exitOf d = none) : time d < 100 := by
  have := Site.pc_le d.site fun r hr => by simp [exitOf, hr] at hx
  have := time_le d
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
