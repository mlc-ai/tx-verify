-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Time
public import Kernels.InklingRelDecode.Proof.Mma.Requests

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX

private theorem mma_hit (s : Mma.Site) : s.pc ∈ Lib.requestPcs ↔
    s = .setMaxReg ∨ s = .setMaxRegInc ∨ s = .dispatch := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

public theorem regBand (d) (inv : Mma.Inv d) :
    (Mma.requestPhase d.site = 1 → Mma.time d = 285) ∧
    (Mma.requestPhase d.site = 2 → 285 < Mma.time d ∧ Mma.time d ≤ Lib.Slots.finish + 280) ∧
    (Mma.requestPhase d.site = 3 → Mma.time d = Lib.Slots.finish + 284) ∧
    (d.site.pc ∈ Lib.requestPcs → Mma.time d =
      [0, 285, Lib.Slots.finish + 280, Lib.Slots.finish + 284].getD
        (Mma.requestPhase d.site) 0) ∧
    (Mma.requestPhase d.site = 2 → d.site.pc ∉ Lib.requestPcs →
      Mma.time d < Lib.Slots.finish + 280) ∧
    (Mma.requestPhase d.site ≠ 2 → d.site.pc ∈ Lib.requestPcs) := by
  obtain ⟨s,i,v⟩ := d
  simp only [Mma.requestPhase, Mma.time, Mma.slotTime, Lib.Slots.finish, Lib.Slots.frame,
    Lib.Slots.stride, Lib.Slots.enter, Lib.Slots.reuse, Lib.Slots.mma, Mma.Inv, mma_hit] at *
  cases s <;> simp_all [Mma.Site.position] <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
