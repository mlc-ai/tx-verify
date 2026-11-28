-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Ref

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX PTX.Flow PTX.Proof Control

theorem final_only (s : Site) (h : s ≠ .wait) : s.pc ≠ 2565 := by
  cases s <;> first | contradiction | decide | (rename_i j; revert j; decide +kernel)

theorem bump_away {ev : Event} (hp : ev.pc ≠ 2565) : okPollAt 2565 ev = false := by
  obtain ⟨p,k⟩ := ev
  cases k <;> try rfl
  rename_i _ _ ok _ _
  cases ok <;> simp_all [okPollAt]

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
