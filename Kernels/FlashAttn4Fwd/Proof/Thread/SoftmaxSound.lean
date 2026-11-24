-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Softmax
public import Lemmas.Flow.Code

@[expose] public section

/-! # The softmax warps as a code machine

Every softmax site is an unguarded event instruction (`site_ok`; the implicit wait of a load
is the load's instruction at sub-step 1). `code` is the role as a code machine on its own (from
`setmaxnreg`, item 0); the machine skeleton composes it through `Site.pc`, `Site.sub`,
`facts`, `Inv` and `next`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The instruction of each softmax site: an unguarded event instruction. -/
theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨s, i, t, sc, m, l⟩ := d
  cases s with
  | setMaxReg => exact ⟨_, Flow.code_setMaxReg_4, rfl, trivial⟩
  | bar0 => exact ⟨_, Flow.code_bar_2, rfl, trivial⟩
  | statsW w =>
    rcases fin4_cases w with rfl | rfl | rfl | rfl
    · exact ⟨_, Flow.code_mbarWait_30, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_32, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_34, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_35, rfl, trivial⟩
  | sW lp =>
    cases lp
    · exact ⟨_, Flow.code_mbarWait_31, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_33, rfl, trivial⟩
  | ld lp c =>
    cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
    · exact ⟨_, Flow.code_tmemLoad_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_2, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_3, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_4, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_5, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_6, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_7, rfl, trivial⟩
  | ldW lp c =>
    cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
    · exact ⟨_, Flow.code_tmemLoad_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_2, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_3, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_4, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_5, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_6, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemLoad_7, rfl, trivial⟩
  | alphaSt => exact ⟨_, Flow.code_store_0, rfl, trivial⟩
  | gen j =>
    rcases fin3_cases j with rfl | rfl | rfl
    · exact ⟨_, Flow.code_barArrive_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_barArrive_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_barArrive_2, rfl, trivial⟩
  | pst lp c =>
    cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
    · exact ⟨_, Flow.code_tmemStore_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemStore_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemStore_2, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemStore_3, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemStore_4, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemStore_5, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemStore_6, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemStore_7, rfl, trivial⟩
  | pwait lp h =>
    cases lp <;> rcases fin2_cases h with rfl | rfl
    · exact ⟨_, Flow.code_tmemWait_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemWait_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemWait_2, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemWait_3, rfl, trivial⟩
  | pArr lp =>
    cases lp
    · exact ⟨_, Flow.code_mbarArrive_10, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_12, rfl, trivial⟩
  | warpBar lp =>
    cases lp
    · exact ⟨_, Flow.code_warpBar_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_warpBar_1, rfl, trivial⟩
  | el lp =>
    cases lp
    · exact ⟨_, Flow.code_elect_52, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_53, rfl, trivial⟩
  | p2Arr lp =>
    cases lp
    · exact ⟨_, Flow.code_mbarArrive_11, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_13, rfl, trivial⟩
  | lSt => exact ⟨_, Flow.code_store_1, rfl, trivial⟩
  | barEnd => exact ⟨_, Flow.code_barArrive_3, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- The softmax role as a code machine. -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) : Flow.Code kernel A L g where
  D := D
  init := start
  pc := (·.site.pc)
  facts := facts L g
  sub := (·.site.sub)
  inv := Inv L g
  next := next L g

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
