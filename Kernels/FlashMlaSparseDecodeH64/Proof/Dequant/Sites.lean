-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.Roles
public import Tactics.KernelRfl

@[expose] public section

/-! # The sites of warpgroup 2 (the dequantizer)

Warpgroup 2 (warps 8–11, pcs 2606–3610 and the `ret` at 3611) has 78 event instructions and the
return. Its sites, read from the PTX:

* **Set-up**: the `setmaxnreg` (`smr`), the two length loads (`lenA`, `lenB`, each skipped for a
  null pointer), the poll of the Q barrier (`wq`, `q_utccp`).
* **Block loop** (pcs 2667–3607): the polls of the raw-ready and SV-done barriers of the slot
  (`wraw`, `wsv`); per row `r` of the thread's four, the 16 scale bytes (`scale r`, one
  `ld.shared.v4.b32`), the eight raw words (`raw r s`, `ld.shared.b64`) and the eight chunk stores
  (`store r s`, `st.shared.b128`); the proxy fence (`fpx`) and the arrivals on the
  dequant-ready and raw-free barriers (`arrD`, `arrF`).
* **End**: named barrier 12 (`bar`) and the return.

A row is 225 instructions after the previous one. Within a row the compiler hoisted each raw load
above the previous step's store: `raw r 0`, `raw r 1`, `store r 0`, `raw r 2`, …, `raw r 7`,
`store r 6`, `store r 7` (`Site.pc`).

`sites_pcs`: the sites' pcs are exactly the region's event instructions (`RoleDecl.sites` of the
region `Common/Sites.lean` names `dequant`, by evaluation of the decoded program). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Flow

inductive Site where
  | smr | lenA | lenB | wq | wraw | wsv
  | scale (r : Fin 4) | raw (r : Fin 4) (s : Fin 8) | store (r : Fin 4) (s : Fin 8)
  | fpx | arrD | arrF | bar | exit
  deriving DecidableEq

/-- The first raw load of row `r`. -/
def rowBase (r : Nat) : Nat := 2729 + 225 * r

def Site.pc : Site → Nat
  | .smr => 2606 | .lenA => 2620 | .lenB => 2630 | .wq => 2644 | .wraw => 2677 | .wsv => 2684
  | .scale r => rowBase r.val - 34
  | .raw r s => if s.val = 0 then rowBase r.val
      else if s.val = 1 then rowBase r.val + 8 else rowBase r.val + 31 + 24 * (s.val - 2)
  | .store r s => rowBase r.val + 23 + 24 * s.val - (if s.val = 7 then 1 else 0)
  | .fpx => 3595 | .arrD => 3597 | .arrF => 3599 | .bar => 3610 | .exit => 3611

/-- A row's sites in program order. -/
def rowSites (r : Fin 4) : List Site :=
  [.scale r, .raw r 0, .raw r 1, .store r 0, .raw r 2, .store r 1, .raw r 3, .store r 2,
    .raw r 4, .store r 3, .raw r 5, .store r 4, .raw r 6, .store r 5, .raw r 7, .store r 6,
    .store r 7]

/-- Every site, in program order. -/
def allSites : List Site :=
  [Site.smr, Site.lenA, Site.lenB, Site.wq, Site.wraw, Site.wsv] ++
    (List.finRange 4).flatMap rowSites ++ [Site.fpx, Site.arrD, Site.arrF, Site.bar, Site.exit]

/-- The role's region (the region `Common/Sites.lean` names `dequant`). -/
def region : RoleDecl := ⟨[(2606, 3612)], [3611]⟩

/-- **The sites are the region's event instructions**, in program order. -/
theorem sites_pcs : allSites.map Site.pc = RoleDecl.sites kernel region := by
  kernel_rfl

/-- The site list has no repetition (so `Site.pc` is injective on it). -/
theorem sites_nodup : (allSites.map Site.pc).Nodup := by
  decide +kernel

/-- Every site is in the region: at pc 2606 or later, at the `ret` (3611) or before it. -/
theorem Site.pc_range (s : Site) : 2606 ≤ s.pc ∧ s.pc ≤ 3611 := by
  cases s with
  | scale r => have := r.isLt; simp only [Site.pc, rowBase]; omega
  | raw r i => have := r.isLt; have := i.isLt; simp only [Site.pc, rowBase]; split_ifs <;> omega
  | store r i => have := r.isLt; have := i.isLt; simp only [Site.pc, rowBase]; split_ifs <;> omega
  | _ => decide

/-- Every site but the `ret` is before it. -/
theorem Site.pc_lt (s : Site) (hx : s ≠ .exit) : s.pc < 3611 := by
  cases s with
  | exit => exact absurd rfl hx
  | scale r => have := r.isLt; simp only [Site.pc, rowBase]; omega
  | raw r i => have := r.isLt; have := i.isLt; simp only [Site.pc, rowBase]; split_ifs <;> omega
  | store r i => have := r.isLt; have := i.isLt; simp only [Site.pc, rowBase]; split_ifs <;> omega
  | _ => decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
