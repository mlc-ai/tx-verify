-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Sites.Decl
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine

@[expose] public section

/-! # The startup's event instructions -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The startup's event instructions: its sites and the first instructions of the roles. -/
def startupSites : List Nat :=
  [25, 34, 35, 46, 50, 51, 56, 60, 61, 62, 66, 67, 68, 73, 77, 78, 79, 80, 84, 85, 90, 94, 95,
    96, 100, 101, 105, 109, 110, 111, 115, 116, 119, 123, 124, 125, 129, 130, 135, 139, 140, 141,
    145, 146, 151, 155, 156, 157, 161, 162, 166, 170, 171, 172, 173, 179, 1907, 2769, 3102, 7746,
    9205]

theorem startup_sites : CodeCheck.sitesFrom startupDecl.region 0 kernel.code = startupSites := by
  kernel_rfl

/-- Every startup site is an event instruction of the region. -/
theorem Startup.site_mem (s : Startup.Site) : s.pc ∈ startupSites := by
  cases s with
  | sh j => fin_cases j <;> decide
  | elect j => fin_cases j <;> decide
  | init n => fin_cases n <;> decide
  | fence => decide
  | bar => decide
  | enter r => cases r <;> decide

end
end PTX.Kernels.TmlFa4Fwd.Proof
