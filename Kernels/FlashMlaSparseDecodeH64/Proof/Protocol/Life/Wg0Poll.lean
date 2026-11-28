-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Exit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Dealloc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar12
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce

@[expose] public section

/-! # A lane of warpgroup 0 that exited has made its poll of `svDone`

A lane of warpgroup 0 of an exited CTA made its barrier-12 event before its exit
(`wg0_exitBar12`) and, before it, its poll of `svDone` at pc 1184 (`wg0_bar12_poll`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A warpgroup-0 lane of an exited CTA polled `svDone` at pc 1184**: the lane `Y` of warpgroup 0
that is first in its CTA. -/
theorem exit_poll1184 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {y0 : Nat}
    (hy0 : y0 < L.threads) (hx : CtaExited L X (y0 / L.block)) :
    ∃ Y jw p, Y < L.threads ∧ Y / L.block = y0 / L.block ∧ warp L Y < 4 ∧
      X.get (Y, jw) = some ⟨1184, .wait (mbarLoc L (y0 / L.block)
        (.svDone (slot2 (blocksOf P L (y0 / L.block) - 1)))) p true true .cta⟩ := by
  have hb : 0 < L.block := by rw [hp.block]; decide
  set y := y0 / L.block * L.block with hydef
  have hyc : y / L.block = y0 / L.block := by rw [hydef]; exact Nat.mul_div_cancel _ hb
  have hy : y < L.threads := by
    have : y ≤ y0 := Nat.div_mul_le_self _ _
    omega
  have hy4 : warp L y < 4 := by
    simp only [warp, tidOf_x_eq hp, hp.block, hydef]
    omega
  obtain ⟨pcx, hlast⟩ := hx y hy hyc
  rw [List.getLast?_eq_getElem?] at hlast
  have hxy : X.get (y, (X.tr y).length - 1) = some ⟨pcx, .exit⟩ := hlast
  have hcnt := wg0_exitBar12 hp hX hFw hy4 hxy
  obtain ⟨j, pcj, hj, -⟩ := barId_nth hR hy (id := 12) (c := 0) (by omega)
  obtain rfl := wg0_bar12_pc hp hX hFw hy4 hj
  obtain ⟨jw, p, -, hpoll⟩ := wg0_bar12_poll hp hX hFw hy4 hj
  rw [hyc] at hpoll
  exact ⟨y, jw, p, hy, hyc, hy4, hpoll⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
