-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Mma producer=B status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The MMA warp's mbarrier row

The MMA lane (warp 4, pcs 1850–2161) touches the mbarriers at 16 sites (`mmaSites`, checked on
the code by `mma_sites`). Over the lane's events before its `k`-th (`es`):

| pc | use | object | parity / bytes |
| - | - | - | - |
| 1906–1927 (8) | tensor load | `qTma` | 8192 bytes |
| 1929 | arrive | `qTma` | tx 65536 |
| 1931 | wait | `qTma` | 0 (first poll) |
| 1982 | commit | `qUtccp` | |
| 1983 | wait | `qUtccp` | 0 (first poll) |
| 2012 | wait | `dequantReady (slot2 (polls2 … dequantReady es))` | `okPolls l es % 2` |
| 2105 | commit | `qkDone (slot2 (cmts2 … qkDone es))` | |
| 2107 | wait | `soReady (slot2 (polls2 … soReady es))` | `okPolls l es % 2` |
| 2148 | commit | `svDone (slot2 (cmts2 … svDone es))` | | -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- Thread `g` is in warp 4 and `pc` is in the MMA code. -/
def MmaAt (L : Launch) (g pc : Nat) : Prop := warp L g = 4 ∧ 1850 ≤ pc ∧ pc < 2162

/-- The pcs of the query's eight tensor loads. -/
def qLoadPcs : List Nat := [1906, 1909, 1912, 1915, 1918, 1921, 1924, 1927]

/-- **The mbarrier uses of the MMA lane**, event `e` of lane `g` at index `k` on `l`. -/
inductive MmaUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | qLoad (hpc : e.pc ∈ qLoadPcs) (hl : l = loc L g .qTma) (hk : Issue e l 8192)
  | qArrive (hpc : e.pc = 1929) (hl : l = loc L g .qTma) (hk : Arrive e l 65536)
  | qWait (hpc : e.pc = 1931) (hl : l = loc L g .qTma) (hk : Wait e l 0)
      (h0 : okPolls l ((X.tr g).take k) = 0)
  | qCommit (hpc : e.pc = 1982) (hl : l = loc L g .qUtccp) (hk : Commit e l)
  | qCopyWait (hpc : e.pc = 1983) (hl : l = loc L g .qUtccp) (hk : Wait e l 0)
      (h0 : okPolls l ((X.tr g).take k) = 0)
  | kvWait (hpc : e.pc = 2012)
      (hl : l = loc L g (.dequantReady (slot2 (polls2 L g .dequantReady ((X.tr g).take k)))))
      (hk : Wait e l (okPolls l ((X.tr g).take k) % 2))
  | qkCommit (hpc : e.pc = 2105)
      (hl : l = loc L g (.qkDone (slot2 (cmts2 L g .qkDone ((X.tr g).take k)))))
      (hk : Commit e l)
  | soWait (hpc : e.pc = 2107)
      (hl : l = loc L g (.soReady (slot2 (polls2 L g .soReady ((X.tr g).take k)))))
      (hk : Wait e l (okPolls l ((X.tr g).take k) % 2))
  | svCommit (hpc : e.pc = 2148)
      (hl : l = loc L g (.svDone (slot2 (cmts2 L g .svDone ((X.tr g).take k)))))
      (hk : Commit e l)

/-- The MMA code's mbarrier sites. -/
def mmaSites : List (Nat × Shape) :=
  qLoadPcs.map (fun pc => (pc, .issue .tile)) ++
    [(1929, .arrive none), (1931, .wait), (1982, .commit), (1983, .wait), (2012, .wait),
      (2105, .commit), (2107, .wait), (2148, .commit)]

/-- **Static check**: the mbarrier sites of pcs 1850–2161 are `mmaSites`. -/
theorem mma_sites : regionOk kernel.code 1850 2162 mmaSites = true := by decide +kernel

end MbarRow

/-- **Row `MbarRow.Mma`**: every event of a warp-4 lane at a pc of the MMA code that names an
mbarrier is one of `MmaUse`. -/
def MbarRow.Mma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    MmaAt L g e.pc → Frame.MbarOf e l → MmaUse L X g k e l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
