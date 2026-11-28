-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Tma producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The TMA warp's mbarrier row

The TMA lane (warp 5, pcs 2162–2331) touches the mbarriers at 22 sites (`tmaSites`, checked on
the code by `tma_sites`). Over the lane's events before its `k`-th (`es`):

| pc | use | object | parity / bytes |
| - | - | - | - |
| 2205 | wait | `qUtccp` | 0 (first poll) |
| 2209 | wait | `lastStoreDone` | 0 (first poll) |
| 2234 | wait | `coordReady (slot4 (polls4 … coordReady es))` | `okPolls l es % 2` |
| 2245 | wait | `rawFree (slot2 (polls2 … rawFree es))` | `(okPolls l es + 1) % 2` |
| 2259–2303 (16) | gather4 load | `rawReady (slot2 (arrs2 … rawReady es))` | 2304 bytes |
| 2305 | arrive | `rawReady (slot2 (arrs2 … rawReady es))` | tx 36864 |
| 2308 | arrive | `coordFree (slot4 (arrs4 … coordFree es))` | tx 0 |

The block's sixteen loads precede its expecting arrival, so a load's slot is counted by the
lane's earlier arrivals on the family, as the arrival's own.

**Proved** by lane A: `mbarRow_tma` (`Tma/Export/Mbar.lean`); the 2304 bytes from the cache maps
of `Pre` (`tma_gather_bytes`, `Common/TmaLen.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- Thread `g` is in warp 5 and `pc` is in the TMA code. -/
def TmaAt (L : Launch) (g pc : Nat) : Prop := warp L g = 5 ∧ 2162 ≤ pc ∧ pc < 2332

/-- The pcs of a block's sixteen gather4 loads. -/
def rawLoadPcs : List Nat :=
  [2259, 2262, 2265, 2268, 2271, 2274, 2277, 2280, 2283, 2286, 2289, 2292, 2295, 2298, 2301,
    2303]

/-- **The mbarrier uses of the TMA lane**, event `e` of lane `g` at index `k` on `l`. -/
inductive TmaUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | qWait (hpc : e.pc = 2205) (hl : l = loc L g .qUtccp) (hk : Wait e l 0)
      (h0 : okPolls l ((X.tr g).take k) = 0)
  | lastWait (hpc : e.pc = 2209) (hl : l = loc L g .lastStoreDone) (hk : Wait e l 0)
      (h0 : okPolls l ((X.tr g).take k) = 0)
  | coordWait (hpc : e.pc = 2234)
      (hl : l = loc L g (.coordReady (slot4 (polls4 L g .coordReady ((X.tr g).take k)))))
      (hk : Wait e l (okPolls l ((X.tr g).take k) % 2))
  | freeWait (hpc : e.pc = 2245)
      (hl : l = loc L g (.rawFree (slot2 (polls2 L g .rawFree ((X.tr g).take k)))))
      (hk : Wait e l ((okPolls l ((X.tr g).take k) + 1) % 2))
  | rawLoad (hpc : e.pc ∈ rawLoadPcs)
      (hl : l = loc L g (.rawReady (slot2 (arrs2 L g .rawReady ((X.tr g).take k)))))
      (hk : Issue e l 2304)
  | rawArrive (hpc : e.pc = 2305)
      (hl : l = loc L g (.rawReady (slot2 (arrs2 L g .rawReady ((X.tr g).take k)))))
      (hk : Arrive e l 36864)
  | coordFree (hpc : e.pc = 2308)
      (hl : l = loc L g (.coordFree (slot4 (arrs4 L g .coordFree ((X.tr g).take k)))))
      (hk : Arrive e l 0)

/-- The TMA code's mbarrier sites. -/
def tmaSites : List (Nat × Shape) :=
  [(2205, .wait), (2209, .wait), (2234, .wait), (2245, .wait)] ++
    rawLoadPcs.map (fun pc => (pc, .issue .fourRows)) ++
    [(2305, .arrive none), (2308, .arrive (some 0))]

/-- **Static check**: the mbarrier sites of pcs 2162–2331 are `tmaSites`. -/
theorem tma_sites : regionOk kernel.code 2162 2332 tmaSites = true := by decide +kernel

end MbarRow

/-- **Row `MbarRow.Tma`**: every event of a warp-5 lane at a pc of the TMA code that names an
mbarrier is one of `TmaUse`. -/
def MbarRow.Tma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    TmaAt L g e.pc → Frame.MbarOf e l → TmaUse L X g k e l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
