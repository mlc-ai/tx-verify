-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Dispatch producer=W status=row-proved domain=consistent ahead=1
module

public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Base

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
namespace MbarRow
open PTX PTX.Flow PTX.MbarRow

def DispatchAt (L : Launch) (g pc : Nat) : Prop :=
  4 ≤ g % L.block / 32 ∧ ((2333 ≤ pc ∧ pc < 2344) ∨
    (2557 ≤ pc ∧ pc < 2560) ∨ (2853 ≤ pc ∧ pc < 2856))

def dispatchSites : List PTX.MbarRow.Site :=
  []

theorem dispatch_sites : regionOk kernel.code 2333 2344 dispatchSites = true := by
  decide +kernel

theorem dispatch_sites_1 : regionOk kernel.code 2557 2560 [] = true := by
  decide +kernel

theorem dispatch_sites_2 : regionOk kernel.code 2853 2856 [] = true := by
  decide +kernel

/-- No instruction in these regions can name an mbarrier. -/
inductive DispatchUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where


end MbarRow

def MbarRow.Dispatch (_Q : Params) (L : Launch) (X : Execution) : Prop :=
  Row L X (DispatchAt L) (DispatchUse L X)

end PTX.Kernels.InklingRelDecode.Proof
