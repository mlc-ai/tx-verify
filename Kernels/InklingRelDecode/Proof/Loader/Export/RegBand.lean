-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Time
public import Kernels.InklingRelDecode.Proof.Loader.Requests

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX

/- site pcs -/
private theorem loader_hit (s : Loader.Site) :
    s.pc ∈ Lib.requestPcs ↔ s = .dec ∨ s = .inc ∨ s = .dispatch := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

public theorem regBand (d) :
    (Loader.requestPhase d.site = 1 → Loader.time d = 285) ∧
    (Loader.requestPhase d.site = 2 → 285 < Loader.time d ∧
      Loader.time d ≤ Lib.Slots.finish + 280) ∧
    (Loader.requestPhase d.site = 3 → Loader.time d = Lib.Slots.finish + 284) ∧
    (d.site.pc ∈ Lib.requestPcs → Loader.time d =
      [0, 285, Lib.Slots.finish + 280, Lib.Slots.finish + 284].getD
        (Loader.requestPhase d.site) 0) ∧
    (Loader.requestPhase d.site = 2 → d.site.pc ∉ Lib.requestPcs →
      Loader.time d < Lib.Slots.finish + 280) ∧
    (Loader.requestPhase d.site ≠ 2 → d.site.pc ∈ Lib.requestPcs) := by
  have lt := Loader.bits_lt d.counter
  have pos := Loader.position_bound d.site
  obtain ⟨s,i,n,a,b⟩ := d
  simp only [Loader.requestPhase, Loader.time, Loader.slotTime, Lib.Slots.finish, Lib.Slots.frame,
    Lib.Slots.stride, Lib.Slots.enter, Lib.Slots.reuse, loader_hit] at *
  cases s <;> simp_all <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
