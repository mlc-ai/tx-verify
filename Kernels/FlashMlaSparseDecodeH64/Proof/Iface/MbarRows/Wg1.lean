-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Wg1 producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # Warpgroup 1's head and idle code: mbarrier row

Warpgroup 1's head (pcs 1842–1849, the dispatch on the warp index) and its idle code (pcs
2587–2605, warp 6 and the lanes of warps 4 and 5 that lost their election) touch no mbarrier
(`wg1_sites`: neither range holds an mbarrier site). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- Thread `g` is a warpgroup-1 lane and `pc` is in the head or the idle code. -/
def Wg1At (L : Launch) (g pc : Nat) : Prop :=
  4 ≤ warp L g ∧ warp L g < 8 ∧ ((1842 ≤ pc ∧ pc < 1850) ∨ (2587 ≤ pc ∧ pc < 2606))

/-- **Static check**: pcs 1842–1849 and 2587–2605 hold no mbarrier site. -/
theorem wg1_sites :
    regionOk kernel.code 1842 1850 [] = true ∧ regionOk kernel.code 2587 2606 [] = true := by
  decide +kernel

end MbarRow

/-- **Row `MbarRow.Wg1`**: no event of the head or the idle code names an mbarrier. -/
def MbarRow.Wg1 (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    Wg1At L g e.pc → Frame.MbarOf e l → False

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
