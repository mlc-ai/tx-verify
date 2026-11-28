-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Dequant producer=D status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # Warpgroup 2's mbarrier row

Warpgroup 2 (warps 8–11, pcs 2606–3610) touches the mbarriers at five sites (`dequantSites`,
checked on the code by `dequant_sites`). Over the lane's events before its `k`-th (`es`):

| pc | use | object | parity |
| - | - | - | - |
| 2644 | wait | `qUtccp` | 0 (first poll) |
| 2677 | wait | `rawReady (slot2 (polls2 … rawReady es))` | `okPolls l es % 2` |
| 2684 | wait | `svDone (slot2 (polls2 … svDone es))` | `(okPolls l es + 1) % 2` |
| 3597 | arrive | `dequantReady (slot2 (arrs2 … dequantReady es))` | tx 0 |
| 3599 | arrive | `rawFree (slot2 (arrs2 … rawFree es))` | tx 0 |

The wait at 2684 is for the PV GEMM that last read the dequantized buffer the block overwrites:
the opposite parity of the block's raw wait, so the first use of each buffer passes at once. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- Thread `g` is a warpgroup-2 lane and `pc` is in warpgroup 2's code. -/
def DequantAt (L : Launch) (g pc : Nat) : Prop :=
  8 ≤ warp L g ∧ warp L g < 12 ∧ 2606 ≤ pc ∧ pc < 3611

/-- **The mbarrier uses of warpgroup 2**, event `e` of lane `g` at index `k` on `l`. -/
inductive DequantUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | qWait (hpc : e.pc = 2644) (hl : l = loc L g .qUtccp) (hk : Wait e l 0)
      (h0 : okPolls l ((X.tr g).take k) = 0)
  | rawWait (hpc : e.pc = 2677)
      (hl : l = loc L g (.rawReady (slot2 (polls2 L g .rawReady ((X.tr g).take k)))))
      (hk : Wait e l (okPolls l ((X.tr g).take k) % 2))
  | svWait (hpc : e.pc = 2684)
      (hl : l = loc L g (.svDone (slot2 (polls2 L g .svDone ((X.tr g).take k)))))
      (hk : Wait e l ((okPolls l ((X.tr g).take k) + 1) % 2))
  | readyArrive (hpc : e.pc = 3597)
      (hl : l = loc L g (.dequantReady (slot2 (arrs2 L g .dequantReady ((X.tr g).take k)))))
      (hk : Arrive e l 0)
  | freeArrive (hpc : e.pc = 3599)
      (hl : l = loc L g (.rawFree (slot2 (arrs2 L g .rawFree ((X.tr g).take k)))))
      (hk : Arrive e l 0)

/-- Warpgroup 2's mbarrier sites. -/
def dequantSites : List (Nat × Shape) :=
  [(2644, .wait), (2677, .wait), (2684, .wait), (3597, .arrive (some 0)),
    (3599, .arrive (some 0))]

/-- **Static check**: the mbarrier sites of pcs 2606–3610 are `dequantSites`. -/
theorem dequant_sites : regionOk kernel.code 2606 3611 dequantSites = true := by decide +kernel

end MbarRow

/-- **Row `MbarRow.Dequant`**: every event of a warpgroup-2 lane at a pc of its code that names
an mbarrier is one of `DequantUse`. -/
def MbarRow.Dequant (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    DequantAt L g e.pc → Frame.MbarOf e l → DequantUse L X g k e l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
