-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Time
public import Kernels.InklingRelDecode.Proof.Mma.Publication
public import Kernels.InklingRelDecode.Proof.Lib.BarClock

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .bar0 ∨ s = .bar1 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem cap2 : Lib.barCap 2 = Lib.Slots.finish + 276 := by simp [Lib.barCap]

private theorem cap3 : Lib.barCap 3 = Lib.Slots.finish + 288 := by simp [Lib.barCap]

private theorem cap1 : Lib.barCap 1 = 289 := by simp [Lib.barCap, Lib.Slots.reuse]

private theorem pos_le (s : Site) : s.position ≤ 28 := by
  cases s <;> simp only [Site.position] <;> omega

/-- **An Mma state's clock against the generations of barrier 1.** -/
public theorem bar_cap {d : D} (hi : Inv d) :
    Lib.BarCapAt (time d) d.site.pc (publicationPhase d.site) := by
  refine ⟨fun hb => ?_, fun h3 => ?_⟩
  · rw [site_hit] at hb
    rcases hb with h | h <;> rw [h] <;> decide
  rw [site_hit]
  have pb := pos_le d.site
  obtain ⟨s, i, v⟩ := d
  have lim := low_lt v
  cases s
  case setMaxReg => simp [time, publicationPhase, cap1, Lib.Slots.enter]
  case ldNum => simp [time, publicationPhase, cap1]
  case bar0 => simp [time, publicationPhase, cap1, Lib.Slots.reuse]
  case bar1 => simp [time, publicationPhase, cap2, Lib.Slots.finish]
  case setMaxRegInc => simp [time, publicationPhase, cap3, Lib.Slots.finish]
  case dispatch => simp [time, publicationPhase, cap3, Lib.Slots.finish]
  case finBar => simp [time, publicationPhase, cap2, Lib.Slots.finish]; omega
  case finElect => simp [time, publicationPhase, cap2, Lib.Slots.finish]; omega
  case finCommit => simp [time, publicationPhase, cap2, Lib.Slots.finish]; omega
  all_goals
    simp only [Inv, D.limit] at hi
    simp only [time, slotTime, Lib.Slots.mma, Lib.Slots.frame, Lib.Slots.finish,
      Lib.Slots.stride, publicationPhase, cap2, Site.position] at pb ⊢
    refine ⟨by omega, by simp, fun _ => by omega⟩

/-- **An Mma state is later than the generation it has passed.** -/
public theorem bar_low (d : D) : Lib.BarLow (time d) (publicationPhase d.site) := by
  intro h1 h4
  obtain ⟨s, i, v⟩ := d
  cases s <;> simp (config := {decide := true}) [time, slotTime, publicationPhase, Site.position,
    Lib.barCap, Lib.Slots.publish, Lib.Slots.reuse, Lib.Slots.enter, Lib.Slots.finish,
    Lib.Slots.mma, Lib.Slots.frame, Lib.Slots.stride] at * <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
