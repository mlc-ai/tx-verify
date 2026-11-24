-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.BarPart
public import Kernels.Fp16Gemm8192.Proof.Progress.BarWaits
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive

@[expose] public section

/-! # Progress at a blocked named barrier wait

A pending consumer whose last event is its arrival on a group's named barrier (its CLC barrier or
output barrier) that is not released (`bar_wait_steps`). Let `N` be its number of arrivals on the
barrier, and `G = N - 1` the generation of its last arrival. The threads of its warp group in its
CTA are the participants (`bar_part`).

* Some participant has fewer than `N` arrivals: it is pending and earlier in the rank table
  (`bar_lag_blocker`).
* Otherwise the participant warps' records that the CTA's history lacks are appended, which
  releases the thread's arrival (`NamedBar.wait_cases`) and lowers its rank by one. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The rank table's time of a thread depends only on the thread's traces. -/
theorem threadTime_congr {Y : Execution} (h : Y.tr = X.tr) (g : Nat) :
    threadTime L Y g = threadTime L X g := by
  simp only [threadTime, exitBase, baseTime, Frame.stateAt, h]

/-- **Progress at a blocked named barrier wait.** A pending consumer whose last event is its arrival
on its group's named barrier (CLC barrier or output barrier), not released, extends a maximal
execution or passes to an obligation of smaller rank: a participant that has made fewer arrivals, or
the same execution with the records of the participant warps that its barrier history lacks
appended, which releases the arrival. -/
theorem bar_wait_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) (hagree : AllResponsesAgree L X)
    (hexit : ClusterExitAll L X) {g : Nat} (hp : Frame.Pending L X g) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c)))) {pc id : Nat}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id (some 128)⟩)
    (hnr : ¬ Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hB : L.block = 384 := hpre.block
  have hb : 0 < L.block := by omega
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hlast
    simp only at this
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hcta : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hg
  -- the thread's state before its last event, and the barrier
  obtain ⟨d0, hd0⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub hlast
  obtain ⟨c0, rfl⟩ := ht.bar_role hg hlast hd0 rfl
  have hout := (ht.cons_out hg hlast hd0).2.2.2.2.1 id (some 128) rfl
  have hwarp := ht.role_warp hg (le_refl _) hσ
  simp only [roleWarp] at hwarp
  obtain ⟨q, hqdef⟩ : ∃ q, q = Consumer.tidOf L g / 32 / 4 := ⟨_, rfl⟩
  have hq2 : q < 2 := by
    simp only [Consumer.tidOf] at hqdef
    omega
  obtain ⟨clc, hid⟩ : ∃ clc : Bool, id = barId clc q := by
    rcases hout with ⟨-, hid, -⟩ | ⟨-, hid, -⟩
    · exact ⟨true, by simp [barId, hid, hqdef]⟩
    · exact ⟨false, by simp [barId, hid, hqdef, Consumer.outId]⟩
  subst hid
  have hσ1 : Frame.stateAt (code L) X g ((X.tr g).length - 1 + 1) = some (some (.inr (.cons c))) :=
    by
    rw [show (X.tr g).length - 1 + 1 = (X.tr g).length by omega]
    exact hσ
  obtain ⟨hxg, hs0⟩ := ht.cons_after_bar hg hlast rfl hd0 hσ1
  have hcl1 : clArrives (X.tr g) = 1 := by
    rw [ht.cl_phase hg hσ]
    exact clPhase_of_loop hxg
  have hP := bar_part ht hub hX hexit (q := q) (clc := clc) hq2 hg hcl1
  have hrank : rank L X (.thread g) = threadTime L X g + 1 := by simp [rank, hnr]
  rcases NamedBar.wait_cases hmax (fun Y => prod_wf Y) (bar_shape hpre clc hq2) hg hP hlast hnr
    with ⟨h, hh, hhc, hhw, hhl⟩ | ⟨Y, hmaxY, hYtr, hrelY⟩
  · -- a participant behind the thread blocks it
    have hgrp : Consumer.tidOf L h / 32 / 4 = q := by
      simp only [Consumer.tidOf]
      exact mem_group.mp hhw
    have hNg := NamedBar.countP_last (id := barId clc q)
      (show (X.tr g)[(X.tr g).length - 1]? = _ from hlast) (by simp [Execution.isBarId])
    exact .inr ⟨X, .thread h, hmax, bar_lag_blocker ht hub hX hagree hexit hg hh hne hhc hσ hxg
      hs0 hqdef.symm hgrp hcl1 hnr rfl (by unfold barCount; omega) hhl⟩
  · -- the records the barrier history lacks are appended, which releases the thread
    refine .inr ⟨Y, .thread g, hmaxY, ⟨hg, fun h => hne (hYtr ▸ h.1),
      fun pc' hl => hp.2.2 pc' (by rwa [hYtr] at hl)⟩, ?_⟩
    rw [rank_released hrelY, threadTime_congr hYtr]
    omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
