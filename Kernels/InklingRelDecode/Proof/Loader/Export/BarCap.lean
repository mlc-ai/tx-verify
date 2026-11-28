-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Time
public import Kernels.InklingRelDecode.Proof.Loader.Publication
public import Kernels.InklingRelDecode.Proof.Lib.BarClock

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .beginBar ∨ s = .endBar := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem cap2 : Lib.barCap 2 = Lib.Slots.finish + 276 := by simp [Lib.barCap]

private theorem cap3 : Lib.barCap 3 = Lib.Slots.finish + 288 := by simp [Lib.barCap]

private theorem cap1 : Lib.barCap 1 = 289 := by simp [Lib.barCap, Lib.Slots.reuse]

private theorem loop_time (s : Site) (d : D) (h : d.site = s) (e : s ≠ .dec) (e1 : s ≠ .first)
    (e2 : s ≠ .second) (e3 : s ≠ .beginBar) (e4 : s ≠ .endBar) (e5 : s ≠ .inc)
    (e6 : s ≠ .dispatch) :
    time d = Lib.Slots.frame (bits d.counter).toNat + s.position := by
  subst h
  unfold time slotTime
  split <;> simp_all

/-- **A Loader state's clock against the generations of barrier 1.** -/
public theorem bar_cap (d : D) : Lib.BarCapAt (time d) d.site.pc (publicationPhase d.site) := by
  refine ⟨fun hb => ?_, fun h3 => ?_⟩
  · rw [site_hit] at hb
    rcases hb with h | h <;> rw [h] <;> decide
  rw [site_hit]
  have lt := bits_lt d.counter
  have pb := position_bound d.site
  obtain ⟨s, c, l, p, q⟩ := d
  cases s
  case dec => simp [time, publicationPhase, cap1, Lib.Slots.enter]
  case first => simp [time, publicationPhase, cap1]
  case second => simp [time, publicationPhase, cap1]
  case beginBar => simp [time, publicationPhase, cap1, Lib.Slots.reuse]
  case endBar => simp [time, publicationPhase, cap2]
  case inc => simp [time, publicationPhase, cap3, Lib.Slots.finish]
  case dispatch => simp [time, publicationPhase, cap3, Lib.Slots.finish]
  all_goals
    rw [loop_time _ ⟨_, c, l, p, q⟩ rfl (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp)]
    rw [show publicationPhase _ = 2 from rfl, cap2]
    simp only [Lib.Slots.frame, Lib.Slots.finish, Lib.Slots.stride] at *
    refine ⟨by omega, by simp, fun _ => by omega⟩

/-- **A Loader state is later than the generation it has passed.** -/
public theorem bar_low (d : D) : Lib.BarLow (time d) (publicationPhase d.site) := by
  intro h1 h4
  have lt := bits_lt d.counter
  obtain ⟨s, c, l, p, q⟩ := d
  cases s <;> simp (config := {decide := true}) [time, slotTime, publicationPhase, Site.position,
    Lib.barCap, Lib.Slots.publish, Lib.Slots.reuse, Lib.Slots.enter, Lib.Slots.finish,
    Lib.Slots.frame, Lib.Slots.stride] at * <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
