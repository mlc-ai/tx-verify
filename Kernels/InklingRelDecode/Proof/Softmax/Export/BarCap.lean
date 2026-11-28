-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.TcLag
public import Kernels.InklingRelDecode.Proof.Softmax.Publication
public import Kernels.InklingRelDecode.Proof.Lib.BarClock

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .bar0 := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

private theorem cap2 : Lib.barCap 2 = Lib.Slots.finish + 276 := by simp [Lib.barCap]

private theorem cap1 : Lib.barCap 1 = 289 := by simp [Lib.barCap, Lib.Slots.reuse]

/-- **A Softmax state's clock against the generations of barrier 1.** -/
public theorem bar_cap {e t} {d : D} (hi : Inv e t d) :
    Lib.BarCapAt (time d) d.site.pc (publicationPhase d.site) := by
  refine ⟨fun hb => ?_, fun _ => ?_⟩
  · rw [site_hit] at hb
    rw [hb]
    decide
  have fin := time_le_finish hi
  rw [site_hit]
  obtain ⟨s, i, v⟩ := d
  simp only at fin ⊢
  cases s
  case setMaxReg =>
    have : time (⟨.setMaxReg, i, v⟩ : D) = 285 := rfl
    rw [show publicationPhase .setMaxReg = 1 from rfl, cap1, this]
    simp
  case bar0 =>
    have : time (⟨.bar0, i, v⟩ : D) = 289 := rfl
    rw [show publicationPhase .bar0 = 1 from rfl, cap1, this]
    simp
  all_goals
    rw [show publicationPhase _ = 2 from rfl, cap2]
    refine ⟨by omega, by simp, fun _ => by omega⟩

/-- **A Softmax state is later than the generation it has passed.** -/
public theorem bar_low (d : D) : Lib.BarLow (time d) (publicationPhase d.site) := by
  intro h1 h4
  obtain ⟨s, i, v⟩ := d
  cases s <;> simp (config := {decide := true}) [time, publicationPhase, Lib.barCap,
    Lib.Slots.publish, Lib.Slots.reuse, Lib.Slots.enter, Lib.Slots.softmax, Lib.Slots.finish,
    Lib.Slots.frame, Lib.Slots.stride] at * <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
