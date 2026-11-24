-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsScheduleRoles
public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin

@[expose] public section

/-! # The exit sites of the roles

A role state at the exit's position is its role's exit site. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

theorem Facts.store_site_ret (s : Store.Site) (h : s.pc ∈ [Flow.exit_0]) : s = .exit := by
  cases s <;> first | rfl | (exfalso; revert h; site_decide)

theorem Facts.mma_site_ret (s : Mma.Site) (h : s.pc ∈ [Flow.exit_0]) : s = .exit := by
  cases s <;> first | rfl | (exfalso; revert h; site_decide)

theorem Facts.soft_site_ret (s : Softmax.Site) (h : s.pc ∈ [Flow.exit_0]) : s = .exit := by
  cases s <;> first | rfl | (exfalso; revert h; site_decide)

theorem Facts.corr_site_ret (s : Correction.Site) (h : s.pc ∈ [Flow.exit_0]) : s = .exit := by
  cases s <;> first | rfl | (exfalso; revert h; site_decide)

end PTX.Kernels.FlashAttn4Fwd.Proof
