-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Lemmas.Flow.Roles
public import Tactics.KernelRfl

@[expose] public section

/-! # The sites of warpgroup 0

Warpgroup 0 (warps 0–3, pcs 103–1841 and the `ret` at 3611) has 129 event instructions and the
return. Its sites are families over the code's repetitions, read from the PTX:

* **Set-up**: the `setmaxnreg` (`smr`), the sink load (`sink`, skipped for a null pointer), the
  two length loads (`lenA`, `lenB`, each skipped for a null pointer), the bulk-group wait and the
  arrival on the last-store barrier (`bwait`, `arrL`).
* **Block loop** (pcs 253–1146): named barrier 9 (`bar0`), the polls of the valid-mask and QK
  barriers (`wv`, `wq`), a `tcgen05` fence (`tcfa`), the two score loads in one of two orders by
  the stage (`sld arm k`), their wait and fence (`sldw`, `tcfb`), the valid-mask word (`vm`),
  eight 16-byte stores to the peer exchange buffer (`pst k`), named barrier 10/11 (`bar1`), eight
  two-element peer reads (`pld k`), the row-maximum exchange (`mst`, `bar2`, `mld`) with the
  arrival freeing the valid-mask slot (`arrV`), the rescale vote (`vote`), four P stores
  (`ost k`), the rescale arm (a fence, then per 64-column chunk `c` a load, its wait, a store and
  its wait: `rld c`, `rldw c`, `rst c`, `rstw c`, then a fence), the proxy fence and the arrival
  on the softmax-ready barrier (`fpx`, `arrS`).
* **Epilogue** (pcs 1147–1841): the row-sum exchange (`ebar0`, `est`, `ebar1`, `eld`), the LSE
  store (`lse`), the poll of the SV barrier and a fence (`wsv`, `efa`), per output chunk `c` the
  accumulator load and its wait (`old c`, `oldw c`), eight 16-byte stores to the staging tile
  (`ost2 c k`), a proxy fence, a named barrier, an election and the elected lane's TMA store
  (`ofpx c`, `obar c`, `oel c`, `otma c`); the bulk commit, the closing named barrier, the
  deallocation and the return.

`sites_pcs`: the sites' pcs are exactly the region's event instructions (`RoleDecl.sites` of the
region `Common/Sites.lean` names `wg0`, by evaluation of the decoded program). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow

inductive Site where
  | smr | sink | lenA | lenB | bwait | arrL
  | bar0 | wv | wq | tcfa | sld (arm : Bool) (k : Fin 2) | sldw | tcfb | vm
  | pst (k : Fin 8) | bar1 | pld (k : Fin 8) | mst | bar2 | arrV | mld | vote | ost (k : Fin 4)
  | rsf | rld (c : Fin 4) | rldw (c : Fin 4) | rst (c : Fin 4) | rstw (c : Fin 4) | rsfb
  | fpx | arrS
  | ebar0 | est | ebar1 | eld | lse | wsv | efa
  | old (c : Fin 4) | oldw (c : Fin 4) | ost2 (c : Fin 4) (k : Fin 8) | ofpx (c : Fin 4)
  | obar (c : Fin 4) | oel (c : Fin 4) | otma (c : Fin 4)
  | commit | ebar | dealloc | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .smr => 103 | .sink => 156 | .lenA => 168 | .lenB => 181 | .bwait => 198 | .arrL => 200
  | .bar0 => 256 | .wv => 264 | .wq => 272 | .tcfa => 275
  | .sld arm k => (if arm then [283, 285] else [278, 280]).getD k.val 0
  | .sldw => 286 | .tcfb => 287 | .vm => 289
  | .pst k => 403 + 10 * k.val | .bar1 => 475 | .pld k => 477 + 5 * k.val
  | .mst => 566 | .bar2 => 569 | .arrV => 571 | .mld => 572 | .vote => 578
  | .ost k => 704 + k.val
  | .rsf => 711
  | .rld c => [716, 817, 918, 1019].getD c.val 0
  | .rldw c => [717, 818, 919, 1020].getD c.val 0
  | .rst c => [814, 915, 1016, 1117].getD c.val 0
  | .rstw c => [815, 916, 1017, 1118].getD c.val 0
  | .rsfb => 1119 | .fpx => 1120 | .arrS => 1122
  | .ebar0 => 1154 | .est => 1155 | .ebar1 => 1156 | .eld => 1157 | .lse => 1178
  | .wsv => 1184 | .efa => 1187
  | .old c => [1201, 1361, 1519, 1676].getD c.val 0
  | .oldw c => [1202, 1362, 1520, 1677].getD c.val 0
  | .ost2 c k => ost2Base c + k.val
  | .ofpx c => [1339, 1499, 1657, 1814].getD c.val 0
  | .obar c => [1342, 1502, 1659, 1817].getD c.val 0
  | .oel c => [1350, 1507, 1664, 1822].getD c.val 0
  | .otma c => [1358, 1516, 1673, 1831].getD c.val 0
  | .commit => 1832 | .ebar => 1835 | .dealloc => 1840 | .exit => 3611

/-- The sites of the Loop half of the proof (pcs 103–1146); the others are the epilogue's. -/
def Site.inLoop (s : Site) : Bool := s.pc < 1147

/-- Every chunk's sites of the rescale arm and of the output. -/
def rsSites (c : Fin 4) : List Site := [Site.rld c, Site.rldw c, Site.rst c, Site.rstw c]
def outSites (c : Fin 4) : List Site :=
  [Site.old c, Site.oldw c] ++ (List.finRange 8).map (Site.ost2 c) ++
    [Site.ofpx c, Site.obar c, Site.oel c, Site.otma c]

/-- Every site, by family, in program order (the two score-load orders interleaved by pc). -/
def allSites : List Site :=
  let a : List Site := [Site.smr, Site.sink, Site.lenA, Site.lenB, Site.bwait, Site.arrL,
    Site.bar0, Site.wv, Site.wq, Site.tcfa, Site.sld false 0, Site.sld false 1, Site.sld true 0,
    Site.sld true 1, Site.sldw, Site.tcfb, Site.vm]
  let b : List Site := (List.finRange 8).map Site.pst ++ [Site.bar1] ++
    (List.finRange 8).map Site.pld ++ [Site.mst, Site.bar2, Site.arrV, Site.mld, Site.vote] ++
    (List.finRange 4).map Site.ost ++ [Site.rsf]
  let c : List Site := (List.finRange 4).flatMap rsSites ++ [Site.rsfb, Site.fpx, Site.arrS,
    Site.ebar0, Site.est, Site.ebar1, Site.eld, Site.lse, Site.wsv, Site.efa]
  let d : List Site := (List.finRange 4).flatMap outSites ++
    [Site.commit, Site.ebar, Site.dealloc, Site.exit]
  a ++ b ++ c ++ d

/-- The role's region (the region `Common/Sites.lean` names `wg0`). -/
def region : RoleDecl := ⟨[(103, 1842), (3611, 3612)], [3611]⟩

/-- **The sites are the region's event instructions**, in program order. -/
theorem sites_pcs : allSites.map Site.pc = RoleDecl.sites kernel region := by
  kernel_rfl

/-- The site list has no repetition (so `Site.pc` is injective on it). -/
theorem sites_nodup : (allSites.map Site.pc).Nodup := by
  decide +kernel

/-- Every site is in the role's code (pcs 103–1841) or the final `ret`. -/
theorem Site.pc_range (s : Site) : (103 ≤ s.pc ∧ s.pc < 1842) ∨ s.pc = 3611 := by
  cases s with
  | sld a k => revert a k; decide
  | pst k | pld k => revert k; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c
    | otma c => revert c; decide
  | ost2 c k => revert c k; decide
  | exit => exact .inr rfl
  | _ => exact .inl ⟨by decide, by decide⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
