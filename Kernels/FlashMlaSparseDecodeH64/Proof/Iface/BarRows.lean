-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Place producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Startup
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Wg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Dequant

@[expose] public section

/-! # The named-barrier classification rows of every role

The rows `BarRow.<Role>` (`Iface/BarRows/<Role>.lean`) classify the barrier events of a lane of
a role at a pc of the role's code, over the regions of the mbarrier rows (`Iface/MbarRows.lean`).
The sixteen sites, by role:

| role | pcs | sites |
| - | - | - |
| `Startup` | 0–102 | 97 (`bar.sync 0`) |
| `Wg0` | 103–1841 | 9 at the eight `wg0NineSites`; `10 + warp % 2` at 475; 12 at 1835 |
| `Wg1` | 1842–1849, 2587–2605 | 12 at 2604 |
| `Mma` | 1850–2161 | 12 at 2160 |
| `Tma` | 2162–2331 | 12 at 2330 |
| `Index` | 2332–2586 | 12 at 2585 |
| `Dequant` | 2606–3610 | 12 at 3610 |

The final `ret` at 3611 holds none (`bar_tail_sites`). **`BarRow.Place`** joins them: a barrier
event of a launched lane is at a pc of one role's range whose lane condition the lane meets (the
dispatch's fact, as `MbarRow.Place`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

end BarRow

/-- **Row `BarRow.Place`**: a barrier event of a launched lane is at a pc of a role's code, and
the lane is of that role. -/
def BarRow.Place (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e →
    Execution.isBar e = true →
    StartupAt e.pc ∨ Wg0At L g e.pc ∨ Wg1At L g e.pc ∨ MmaAt L g e.pc ∨ TmaAt L g e.pc ∨
      IndexAt L g e.pc ∨ DequantAt L g e.pc

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
