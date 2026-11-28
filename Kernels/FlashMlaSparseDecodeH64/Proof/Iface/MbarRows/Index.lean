-- SPDX-License-Identifier: Apache-2.0
-- iface: MbarRow.Index producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The index warp's mbarrier row

The index warp (warp 7, pcs 2332–2586) touches the mbarriers at four sites (`indexSites`, checked
on the code by `index_sites`), two in each of its block loops (the main cache's and the extra
cache's, which continue one ring). Over the lane's events before its `k`-th (`es`):

| pc | use | object | parity |
| - | - | - | - |
| 2446, 2534 | wait | `coordFree (slot4 (polls4 … coordFree es))` | `(okPolls l es + 1) % 2` |
| 2476, 2565 | arrive | `coordReady (slot4 (arrs4 … coordReady es))` | tx 0 | -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace MbarRow

/-- Thread `g` is in warp 7 and `pc` is in the index code. -/
def IndexAt (L : Launch) (g pc : Nat) : Prop := warp L g = 7 ∧ 2332 ≤ pc ∧ pc < 2587

/-- **The mbarrier uses of an index lane**, event `e` of lane `g` at index `k` on `l`. -/
inductive IndexUse (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop where
  | freeWait (hpc : e.pc = 2446 ∨ e.pc = 2534)
      (hl : l = loc L g (.coordFree (slot4 (polls4 L g .coordFree ((X.tr g).take k)))))
      (hk : Wait e l ((okPolls l ((X.tr g).take k) + 1) % 2))
  | readyArrive (hpc : e.pc = 2476 ∨ e.pc = 2565)
      (hl : l = loc L g (.coordReady (slot4 (arrs4 L g .coordReady ((X.tr g).take k)))))
      (hk : Arrive e l 0)

/-- The index code's mbarrier sites. -/
def indexSites : List (Nat × Shape) :=
  [(2446, .wait), (2476, .arrive (some 0)), (2534, .wait), (2565, .arrive (some 0))]

/-- **Static check**: the mbarrier sites of pcs 2332–2586 are `indexSites`. -/
theorem index_sites : regionOk kernel.code 2332 2587 indexSites = true := by decide +kernel

end MbarRow

/-- **Row `MbarRow.Index`**: every event of a warp-7 lane at a pc of the index code that names
an mbarrier is one of `IndexUse`. -/
def MbarRow.Index (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {l : Loc}, g < L.threads → X.get (g, k) = some e →
    IndexAt L g e.pc → Frame.MbarOf e l → IndexUse L X g k e l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
