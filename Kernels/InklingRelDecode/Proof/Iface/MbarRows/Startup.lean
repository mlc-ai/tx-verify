-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Startup producer=C status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
namespace MbarRow
open PTX PTX.Flow PTX.MbarRow

def StartupAt (_L : Launch) (_g pc : Nat) : Prop :=
  (pc < 27 ∨ (2331 ≤ pc ∧ pc < 2333))

def startupSites : List PTX.MbarRow.Site :=
  []

theorem startup_sites : regionOk kernel.code 0 27 startupSites = true := by
  decide +kernel

theorem startup_sites_1 : regionOk kernel.code 2331 2333 [] = true := by
  decide +kernel

/-- No instruction in these regions can name an mbarrier. -/
inductive StartupUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where


end MbarRow

def MbarRow.Startup (_Q : Params) (L : Launch) (X : Execution) : Prop :=
  Row L X (StartupAt L) (StartupUse L X)

end PTX.Kernels.InklingRelDecode.Proof
