-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Time
public import Kernels.InklingRelDecode.Proof.Epilogue.Publication
public import Kernels.InklingRelDecode.Proof.Lib.BarClock

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow Control

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .join ∨ s = .sync1 := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

private theorem cap2 : Lib.barCap 2 = Lib.Slots.finish + 276 := by simp [Lib.barCap]

private theorem cap3 : Lib.barCap 3 = Lib.Slots.finish + 288 := by simp [Lib.barCap]

/-- **An Epilogue state's clock against the generations of barrier 1.** -/
public theorem bar_cap (d : D) : Lib.BarCapAt (time d) d.site.pc (publicationPhase d.site) := by
  refine ⟨fun hb => ?_, fun h3 => ?_⟩
  · rw [site_hit] at hb
    rcases hb with h | h <;> rw [h] <;> decide
  rw [site_hit]
  obtain ⟨s, v⟩ := d
  cases s
  case store k =>
    have := k.isLt
    simp only [time, startTime, publicationPhase, Site.position, cap2]
    exact ⟨by omega, by simp, fun _ => by omega⟩
  all_goals
    simp only [time, startTime, publicationPhase, Site.position, cap2, cap3] at h3 ⊢
    first | (exfalso; omega) | simp

/-- **An Epilogue state is later than the generation it has passed.** -/
public theorem bar_low (d : D) : Lib.BarLow (time d) (publicationPhase d.site) := by
  intro h1 h4
  obtain ⟨s, v⟩ := d
  cases s <;> simp (config := {decide := true}) [time, startTime, publicationPhase, Site.position,
    Lib.barCap, Lib.Slots.reuse, Lib.Slots.finish, Lib.Slots.frame, Lib.Slots.stride] at *
  all_goals omega

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
