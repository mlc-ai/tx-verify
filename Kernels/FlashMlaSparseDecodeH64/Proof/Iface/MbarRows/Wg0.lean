-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Wg0 producer=W1 status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # Warpgroup 0's mbarrier row

Warpgroup 0 (warps 0–3, pcs 103–1841) touches the mbarriers at six sites (`wg0Sites`, checked on
the code by `wg0_sites`). Over the lane's events before its `k`-th (`es`), with `b` the number of
blocks whose QK completion it has seen (`polls2 … qkDone es`):

| pc | use | object | parity / bytes |
| - | - | - | - |
| 200 | arrive | `lastStoreDone` | tx 0 |
| 264 | wait | `coordReady (slot4 (polls4 … coordReady es))` | `okPolls l es % 2` |
| 272 | wait | `qkDone (slot2 (polls2 … qkDone es))` | `okPolls l es % 2` |
| 571 | arrive | `coordFree (slot4 (arrs4 … coordFree es))` | tx 0 |
| 1122 | arrive | `soReady (slot2 (arrs2 … soReady es))` | tx 0 |
| 1184 | wait | `svDone (slot2 (b - 1))` | `(b - 1) / 2 % 2` |

The epilogue's wait at 1184 is the PV completion of the last block (`b - 1`; with no block the
code polls slot 0 with parity 0, which `b - 1 = 0` also gives). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- Thread `g` is a warpgroup-0 lane and `pc` is in warpgroup 0's code. -/
def Wg0At (L : Launch) (g pc : Nat) : Prop := warp L g < 4 ∧ 103 ≤ pc ∧ pc < 1842

/-- **The mbarrier uses of warpgroup 0**, event `e` of lane `g` at index `k` on `l`. -/
inductive Wg0Use (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | lastStore (hpc : e.pc = 200) (hl : l = loc L g .lastStoreDone) (hk : Arrive e l 0)
  | coordReady (hpc : e.pc = 264)
      (hl : l = loc L g (.coordReady (slot4 (polls4 L g .coordReady ((X.tr g).take k)))))
      (hk : Wait e l (okPolls l ((X.tr g).take k) % 2))
  | qkDone (hpc : e.pc = 272)
      (hl : l = loc L g (.qkDone (slot2 (polls2 L g .qkDone ((X.tr g).take k)))))
      (hk : Wait e l (okPolls l ((X.tr g).take k) % 2))
  | coordFree (hpc : e.pc = 571)
      (hl : l = loc L g (.coordFree (slot4 (arrs4 L g .coordFree ((X.tr g).take k)))))
      (hk : Arrive e l 0)
  | soReady (hpc : e.pc = 1122)
      (hl : l = loc L g (.soReady (slot2 (arrs2 L g .soReady ((X.tr g).take k)))))
      (hk : Arrive e l 0)
  | svDone (hpc : e.pc = 1184)
      (hl : l = loc L g (.svDone (slot2 (polls2 L g .qkDone ((X.tr g).take k) - 1))))
      (hk : Wait e l ((polls2 L g .qkDone ((X.tr g).take k) - 1) / 2 % 2))

/-- Warpgroup 0's mbarrier sites. -/
def wg0Sites : List (Nat × Shape) :=
  [(200, .arrive (some 0)), (264, .wait), (272, .wait), (571, .arrive (some 0)),
    (1122, .arrive (some 0)), (1184, .wait)]

/-- **Static check**: the mbarrier sites of pcs 103–1841 are `wg0Sites`. -/
theorem wg0_sites : regionOk kernel.code 103 1842 wg0Sites = true := by decide +kernel

end MbarRow

/-- **Row `MbarRow.Wg0`**: every event of a warpgroup-0 lane at a pc of its code that names an
mbarrier is one of `Wg0Use`. -/
def MbarRow.Wg0 (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    Wg0At L g e.pc → Frame.MbarOf e l → Wg0Use L X g k e l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
