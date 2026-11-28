-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Time
public import Kernels.InklingRelDecode.Proof.Epilogue.MeasureNext
public import Kernels.InklingRelDecode.Proof.Epilogue.TcCount
public import Kernels.InklingRelDecode.Proof.Lib.TcVec

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow Control

/-- **A step of the epilogue control never lowers the clock, and raises it at the load, its wait
and the deallocation.** -/
public theorem time_next {e L g d dn ev} (h : Control.next e L g d ev = some (some dn)) :
    time d ≤ time dn ∧ (d.site.pc = 2607 ∨ d.site.pc = 2608 ∨ d.site.pc = 2851 ∨
      d.site.pc = 2846 ∨ d.site.pc = 2849 ∨ d.site.pc = 2850 → time d < time dn) := by
  have m := measure_next h
  have b1 := position_bound dn.site
  have b2 := position_bound d.site
  refine ⟨?_, fun hm => ?_⟩
  · unfold time measure at *; omega
  · obtain ⟨s, v⟩ := d
    cases s <;> simp only [Site.pc, storePc] at hm <;> try omega
    all_goals simp only [Control.next] at h
    all_goals cases h
    · simp only [time, Site.position]; omega
    · have gate : ∀ a b, 3 < (firstStore a b).position := by
        intro a b; cases a <;> cases b <;> decide
      have := gate e.valid (lead (g % L.block))
      simp only [time, Site.position] at *; omega
    all_goals first | (simp only [time, Site.position]; omega) |
      (split <;> simp only [time, Site.position] <;> omega)

/-- An epilogue clock is at least the epilogue's start, above every loop clock before it. -/
public theorem time_fin (d : D) : 1266 ≤ Lib.Slots.finish ∧ Lib.Slots.finish ≤ time d :=
  ⟨by simp [Lib.Slots.finish, Lib.Slots.frame, Lib.Slots.stride], Nat.le_add_right ..⟩

/-- **A lane of a CTA with the same earlier collective events as a lane at an epilogue collective
is no later**, unless it has passed the deallocation. -/
public theorem epi_lag {dh dE : D} {sk : Bool}
    (hE : dE.site = .load ∨ dE.site = .waitLd ∨ dE.site = .dealloc)
    (v1 : epiCount sk dh.site 2607 = epiCount sk dE.site 2607)
    (v2 : epiCount sk dh.site 2608 = epiCount sk dE.site 2608)
    (live : (dh.site = .shfl ∨ dh.site = .load ∨ dh.site = .waitLd) → sk = false)
    (liveE : (dE.site = .shfl ∨ dE.site = .load ∨ dE.site = .waitLd) → sk = false)
    (nex : dh.site = .exit → dE.site ≠ .dealloc) :
    time dh ≤ time dE ∧ (¬ (dh.site.pc = 2607 ∨ dh.site.pc = 2608 ∨ dh.site.pc = 2851) →
      time dh < time dE) := by
  obtain ⟨s, v⟩ := dh
  obtain ⟨sE, vE⟩ := dE
  simp only at hE v1 v2 live liveE nex ⊢
  rcases hE with rfl | rfl | rfl <;> cases sk <;> cases s <;>
    simp (config := {decide := true}) [epiCount, afterLoad, afterWaitLd, time, startTime,
      Site.position, Site.pc, storePc] at * <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
