-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Startup producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The startup's mbarrier row

Every thread runs the startup (pcs 0–102); its only mbarrier sites are the 23 initializations of
pcs 39–86 (`startupSites`, checked on the code by `startup_sites`), run by the elected lane of
warp 0. The `j`-th initialization of the lane (`j` its earlier initializations) initializes the
family `MbarFam.ofInit j` of its CTA with the family's count. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- `pc` is in the startup's code (every thread runs it). -/
def StartupAt (pc : Nat) : Prop := pc < 103

/-- **The mbarrier uses of the startup**: the lane is in warp 0 and the event is its `j`-th
initialization, of family `MbarFam.ofInit j` with its count. -/
def StartupUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop :=
  warp L g = 0 ∧ ∃ j : Fin 23, j.val = ((X.tr g).take k).countP isMbInit ∧
    l = loc L g (MbarFam.ofInit j) ∧ e.kind = .mbInit l (MbarFam.ofInit j).count

/-- The startup's mbarrier sites: the 23 initializations. -/
def startupSites : List (Nat × Shape) :=
  [39, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 71, 74, 76, 78, 80, 82, 84,
    86].map fun pc => (pc, .init)

/-- **Static check**: the mbarrier sites of pcs 0–102 are `startupSites`. -/
theorem startup_sites : regionOk kernel.code 0 103 startupSites = true := by decide +kernel

end MbarRow

/-- **Row `MbarRow.Startup`**: every startup event that names an mbarrier is an initialization
of `StartupUse`. -/
def MbarRow.Startup (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    StartupAt e.pc → Frame.MbarOf e l → StartupUse L X g k e l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
