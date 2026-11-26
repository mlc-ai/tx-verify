-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # Warpgroup 0's named-barrier events by site

A barrier event of a warpgroup-0 state (`evK_bar`) is barrier 9 of 128 threads at one of the
eight `wg0_sync` pcs, the warp pair's barrier `barW w` of 64 threads at pc 475, or barrier 12 at
pc 1835, whose count register holds the CTA's size and so carries no count. For the warp word the
pair's barrier is `10 + warp % 2` (`barW_warp`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The barrier events of the sites.** -/
theorem evK_bar {w : BitVec 64} {d : D} {e : Event} (hu : ∀ f, e.kind ≠ .ub f)
    (hev : EvK P L g w d e) (hb : Execution.isBar e = true) :
    (d.site.pc ∈ [256, 569, 1154, 1156, 1342, 1502, 1659, 1817] ∧
        e.kind = .bar 9 (some 128) .sync) ∨
      (d.site.pc = 475 ∧ e.kind = .bar (barW w).toNat (some 64) .sync) ∨
      (d.site.pc = 1835 ∧ e.kind = .bar 12 none .sync) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, k⟩ := e
  simp only at hu ⊢
  cases s
  case obar c =>
    simp only [EvK] at hev
    subst hev
    fin_cases c <;> simp [Site.pc]
  all_goals
    simp only [EvK, GWrAt, RdAt, WrAt, GenWrAt, NcEv, TcLdEv, TcStEv, PollEv, ArrEv] at hev
    (try casesm* _ ∨ _, _ ∧ _, Exists _) <;> subst_vars <;> simp_all [Execution.isBar, Site.pc]

/-- The warp pair's barrier of the launch's warp word is `10 + warp % 2`. -/
theorem barW_warp (hp : Pre P L m) : (barW (warpW L g)).toNat = 10 + MbarRow.warp L g % 2 := by
  have hw : MbarRow.warp L g = warpOf L g := by
    simp only [MbarRow.warp, warpOf, tidOf_x_eq hp, tidOf_eq hp]
  have hl := warpOf_lt hp (g := g)
  rw [hw, show warpW L g = BitVec.ofNat 64 (warpOf L g) from rfl]
  generalize warpOf L g = n at hl ⊢
  interval_cases n <;> decide

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
