-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # Barrier 0 on the time table

The startup's `bar.sync 0` (pc 97) is at time `99` (`Startup.time`: two above the pc) and is its
thread's first barrier-0 event (`bar0_at`). A lane without a barrier-0 event has not exited
(`bar0_exit`) and its time is at most `99` (`bar0_lag`): its states are the startup's (a role's
state has passed the barrier), each at or before pc 97, and a lane stopped after its last event
is before the barrier, whose event is barrier 0. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The barrier-0 indicator is `isBarId 0`. -/
theorem isBar0_barId : isBar0 = Execution.isBarId 0 := by
  funext e
  obtain ⟨pc, k⟩ := e
  cases k <;> try rfl
  rename_i id _ _
  cases id <;> rfl

/-- **The startup's barrier event** is at time `99` and has no barrier-0 event before it. -/
theorem bar0_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {j pc : Nat} {cnt : Option Nat} {md : BarMode}
    {σ : (thread P L g).D} (he : X.get (g, j) = some ⟨pc, .bar 0 cnt md⟩)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ)) :
    time P L g σ = 99 ∧ ((X.tr g).take j).countP (Execution.isBarId 0) = 0 := by
  have hg := Frame.lt_of_get hX he
  have hpc : pc = 97 := by
    rcases bar_use hR hg he rfl with ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ |
      ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact h
    · simp only [BarRow.Wg0Use, BarRow.Sync, BarRow.Everyone, Kind.bar.injEq] at h
      omega
    all_goals simp only [Kind.bar.injEq] at h; omega
  subst hpc
  have hub : ∀ f, Kind.bar 0 cnt md ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ', hσ', hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ'
  cases hσ'
  obtain ⟨d, n, rfl, -, -, -, -, hd⟩ := startup_state hJ hi hev hpc' (by simp)
  obtain ⟨-, -, -, -, -, h0, -⟩ := startup_at hp hX hFw he hub (by simp)
  refine ⟨?_, by rw [← isBar0_barId]; exact h0⟩
  simp only at hd
  simp only [time]
  rw [Startup.time_of_ne fun h => by rw [h] at hd; simp [Startup.Site.pc] at hd]
  omega

/-- **A lane without a barrier-0 event** has not exited and is at time at most `99`. -/
theorem bar0_lag (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {y : Nat} (hy : y < L.threads)
    (h0 : (X.tr y).countP (Execution.isBarId 0) = 0) :
    (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧ Sched.threadTime (timed P L) X y ≤ 99 := by
  have hle : ∀ k, ((X.tr y).take k).countP isBar0 = 0 := fun k => by
    have := (List.take_sublist k (X.tr y)).countP_le (p := isBar0)
    rw [isBar0_barId] at this ⊢
    omega
  refine ⟨fun k pc hx => ?_, ?_⟩
  · have := bar0_exit hp hX hFw hx
    rw [hle k] at this
    omega
  refine time_last (Q := fun t => t ≤ 99) (by omega) (fun σ hs => ?_) (fun σ f hs hf _ => ?_)
  · obtain ⟨s, n⟩ := σ
    have hJ := (follow_iff.mp hFw y hy _).2 _ hs
    have hn : n .bar0 = 0 := (state_count hs .bar0).trans (hle _)
    rcases s with d | ⟨i | r, d⟩
    · have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hs
      have := Startup.time_lt hx
      simp only [time] at this ⊢
      omega
    · have : 1 ≤ n .bar0 := by cases i <;> exact hJ.1
      omega
    · exact hJ.elim
  · have hget : X.get (y, (X.tr y).length - 1) = some f := hf
    have hub : ∀ u, f.kind ≠ .ub u := noUb_kind hnu hget
    obtain ⟨σ', hσ', hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw hget hub
    rw [hs] at hσ'
    cases hσ'
    by_cases hlo : f.pc ≤ 97
    · obtain ⟨d, n, rfl, -, -, hE, hx, hd⟩ := startup_state hJ hi hev hpc' (by omega)
      have hne : d.site.pc ≠ 97 := by
        intro h97
        have hb := Startup.Site.eq_bar (fun r hr => by simp [Startup.exitOf, hr] at hx) h97
        have hk : f.kind = .bar 0 none .sync := by
          obtain ⟨site, x1, x2⟩ := d
          simp only at hb
          subst hb
          exact hE
        have hpos : 0 < (X.tr y).countP (Execution.isBarId 0) :=
          List.countP_pos_iff.mpr ⟨f, List.mem_of_getElem? hf, by
            obtain ⟨pc, kd⟩ := f
            simp only at hk
            subst hk
            rfl⟩
        omega
      have := Startup.Site.pc_le d.site fun r hr => by simp [Startup.exitOf, hr] at hx
      have := Startup.time_le d
      simp only [time]
      omega
    · have := bar0_before hp hX hFw hget hub (by omega)
      rw [hle] at this
      omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
