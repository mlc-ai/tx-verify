-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Time
public import Kernels.InklingRelDecode.Proof.Prologue.Publication
public import Kernels.InklingRelDecode.Proof.Lib.BarClock

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .bar18 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem idx_lt (s : Site) : s ≠ .bar18 → s ≠ .exit → allSites.idxOf s < 181 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **A Prologue state's clock against the generations of barrier 1.** -/
public theorem bar_cap (d) :
    Lib.BarCapAt (time d) d.site.pc (publicationPhase d.site) := by
  refine ⟨fun hb => ?_, fun _ => ?_⟩
  · rw [site_hit] at hb
    rw [hb]
    decide
  rw [site_hit]
  obtain ⟨s, a, b, c, w, r⟩ := d
  by_cases h1 : s = .bar18
  · subst h1
    have := last_bar_time a b c w r
    simp [this, publicationPhase, Lib.barCap, Lib.Slots.publish]
  by_cases h2 : s = .exit
  · subst h2
    have ex : allSites.idxOf Site.exit = 182 := by decide +kernel
    have : time (⟨.exit, a, b, c, w, r⟩ : Control.D) = 282 := by
      simp [time, Lib.Slots.prologue, ex]
    simp [this, publicationPhase, Lib.barCap, Lib.Slots.reuse]
  have := idx_lt s h1 h2
  have e : publicationPhase s = 0 := by simp [publicationPhase, h2]
  have c0 : Lib.barCap 0 = 281 := by simp [Lib.barCap, Lib.Slots.publish]
  have t : time (⟨s, a, b, c, w, r⟩ : Control.D) = 100 + allSites.idxOf s := rfl
  simp only [e, c0, t]
  exact ⟨by omega, fun h => absurd h h1, fun _ => by omega⟩

/-- **A Prologue state is later than the generation it has passed.** -/
public theorem bar_low (d) : Lib.BarLow (time d) (publicationPhase d.site) := by
  intro h1 h4
  obtain ⟨s, a, b, c, w, r⟩ := d
  have : s = .exit := by
    by_contra h
    simp [publicationPhase, h] at h1
  subst this
  have ex : allSites.idxOf Site.exit = 182 := by decide +kernel
  simp [time, publicationPhase, Lib.barCap, Lib.Slots.publish, Lib.Slots.prologue, ex]

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
