-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Place producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0

@[expose] public section

/-! # The mbarrier classification rows of every role

The rows `MbarRow.<Role>` (`Iface/MbarRows/<Role>.lean`) classify the mbarrier events of a lane
of a role at a pc of the role's code. Their pc ranges cover the code but for the final `ret` at
3611, which holds no mbarrier site (`tail_sites`):

| role | lanes (`warp`) | pcs |
| - | - | - |
| `Startup` | all | 0–102 |
| `Wg0` | 0–3 | 103–1841 |
| `Wg1` | 4–7 | 1842–1849, 2587–2605 |
| `Mma` | 4 | 1850–2161 |
| `Tma` | 5 | 2162–2331 |
| `Index` | 7 | 2332–2586 |
| `Dequant` | 8–11 | 2606–3610 |

**`MbarRow.Place`** joins them: an event of a launched lane that names an mbarrier is at a pc of
one of these ranges whose lane condition the lane meets. It is the dispatch's fact (the startup
enters warpgroup 0, 1 or 2 on the warpgroup index, warpgroup 1 its sub-roles on the warp index and
the election, and every region is closed up to its exits, `Common/Sites.lean`), not a role's. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- **Static check**: the final `ret` holds no mbarrier site, and the code ends there. -/
theorem tail_sites : regionOk kernel.code 3611 3612 [] = true ∧ kernel.code.length = 3612 := by
  decide +kernel

end MbarRow

/-- **Row `MbarRow.Place`**: an event of a launched lane that names an mbarrier is at a pc of a
role's code, and the lane is of that role. -/
def MbarRow.Place (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    Frame.MbarOf e l →
    StartupAt e.pc ∨ Wg0At L g e.pc ∨ Wg1At L g e.pc ∨ MmaAt L g e.pc ∨ TmaAt L g e.pc ∨
      IndexAt L g e.pc ∨ DequantAt L g e.pc

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
