-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.LibBar
public import Kernels.InklingRelDecode.Proof.Progress.WfRelease

@[expose] public section

/-!
# A blocked `bar.sync` of named barrier 0 steps: the early and the loop generations

`bar_steps_group` (`LibBar.lean`) needs one group for the whole barrier. Barrier 0 has three
(`NamedBar.PhSources`): all warps without a count (source ordinals 0 and 1), the four default
warps with the count 128 (the loop), all warps again (the last generation). `bar_steps_phased` is
its argument with the release of `NamedBar.sync_release_phased`: a blocked `bar.sync` of a group
whose participants are loop warps or whose ordinal is below `start` either has a participant lane
that has not made the arrival of its ordinal (pending, and earlier by the `time` facts `hlag`,
`hafter`), or every participant has, and a maximal execution with the same traces releases it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A blocked `bar.sync` of a phased barrier steps** when its group is the loop group or its
ordinal is below `start` (`bar_steps_group` with the release `sync_release_phased`). -/
theorem bar_steps_phased {D : Finset Nat} {cD : Option Nat} {start nD : Nat}
    (hD : D ⊆ Finset.range (CtaBarrier.warps L.block)) (hcard : D.card = nD)
    (hnD : nD ≠ CtaBarrier.warps L.block) (hcD : CtaBarrier.target L.block cD = .ok nD)
    {id : Nat} (hS : NamedBar.PhSources L X D cD start id) {count : Option Nat}
    {p : Finset Nat} (hG : NamedBar.Shape L count p id)
    (hs : SafeGoal kernel asms L mem0) (hmax : Maximal L kernel asms mem0 X) {g pc : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hgp : g % L.block / 32 ∈ p)
    (hgw : ∀ w ∈ p, w ∈ D ∨
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) < start)
    (hcnt : ∀ y j pc' cnt' m, y < L.threads → y / L.block = g / L.block →
      y % L.block / 32 ∈ p → X.get (y, j) = some ⟨pc', .bar id cnt' m⟩ →
      ((X.tr y).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) → cnt' = count)
    {d : TSt} (hd : St Q L X g ((X.tr g).length - 1) = some (some d))
    (hafter : (∃ d', St Q L X g ((X.tr g).length - 1 + 1) = some (some d') ∧ T g d < T g d') ∨
      St Q L X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block → y % L.block / 32 ∈ p →
      (X.tr y).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc := NamedBar.cta_lt hg
  have hgt : T g d < Sched.threadTime (timed T Q L) X g :=
    Sched.threadTime_after (M := timed T Q L) hlen hd hafter
  by_cases hA : ∃ y, y < L.block ∧ y / 32 ∈ p ∧
      (X.tr (g / L.block * L.block + y)).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)
  · obtain ⟨y, hy, hyp, hle⟩ := hA
    have hyt := NamedBar.cta_thread_lt hc hy
    have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
    have hmod := (NamedBar.lane_cta (c := g / L.block) hb hy).2
    obtain ⟨hnx, hlt⟩ := hlag _ hyt hdiv (by rw [hmod]; exact hyp) hle
    exact Sched.earlier_steps hmax hnr (pending_of_noExit hX hyt hnx) (by omega)
  · push Not at hA
    obtain ⟨Y, hY, htr, hrel⟩ := NamedBar.sync_release_phased hmax asms_wfStep
      (fun Y hY => fault_unsafe hs hY) hD hcard hnD hcD hS hG hg hgp hlast hgw (fun y hy hyp => by
        obtain ⟨j, ev, hj, hq, hjo⟩ :=
          NamedBar.exists_ordinal (Execution.isBarId id) _ (hA y hy hyp)
        obtain ⟨pcj, cntj, mj, rfl⟩ := NamedBar.isBarId_form hq
        have hget : X.get (g / L.block * L.block + y, j) = some ⟨pcj, .bar id cntj mj⟩ := hj
        have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
        have hmod := (NamedBar.lane_cta (c := g / L.block) hb hy).2
        have hcj := hcnt _ j pcj cntj mj (NamedBar.cta_thread_lt hc hy) hdiv
          (by rw [hmod]; exact hyp) hget hjo
        subst hcj
        exact ⟨j, pcj, mj, hget, hjo⟩)
    exact Sched.same_trace_steps hp hne hnr hY htr hrel

/-! ### The instances of named barrier 0 -/

/-- The group of the early generations: all eight warps, no count. -/
theorem bar0_shape (hpre : Pre Q L mem0) :
    NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) 0 := by
  obtain ⟨hpos, hcount, hcard, hbound⟩ := Bar.bar0_group hpre
  exact ⟨by rw [hcard]; exact hpos, by rw [hcard]; exact hcount, hbound, by decide⟩

/-- The group of the loop generations: the four default warps, the count 128. -/
theorem bar0_loop_shape (hpre : Pre Q L mem0) :
    NamedBar.Shape L (some 128) Bar.loopGroup 0 := by
  have hb : L.block = 256 := hpre.block
  refine ⟨by simp [Bar.loopGroup], by rw [Bar.loopGroup_card]; exact Bar.loopGroup_target,
    fun w hw => ?_, by decide⟩
  simp only [Bar.loopGroup, Finset.mem_range] at hw
  omega

/-- **A blocked `bar.sync 0` of the early generations steps** (source ordinal below 2, all warps,
no count), given the `time` facts of the participant lanes. -/
theorem bar0_early_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hmax : Maximal L kernel asms mem0 X)
    (ht : Frame.Tracked (code L Q) X) {g pc : Nat} (hp : Frame.Pending L X g)
    (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) 0 none pc)
    (hG : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) < 2) {d : TSt}
    (hd : St Q L X g ((X.tr g).length - 1) = some (some d))
    (hafter : (∃ d', St Q L X g ((X.tr g).length - 1 + 1) = some (some d') ∧ T g d < T g d') ∨
      St Q L X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block →
      (X.tr y).countP (Execution.isBarId 0) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hb : L.block = 256 := hpre.block
  have hX := hmax.1
  refine bar_steps_phased (Bar.loopGroup_sub hpre) Bar.loopGroup_card (Bar.loopGroup_ne hpre)
    Bar.loopGroup_target (Bar.bar0_sources hpre hX hS ht) (bar0_shape hpre) hs hmax hp hnr hlen
    hlast ?_ (fun _ _ => .inr hG) ?_ hd hafter (fun y hy hdiv _ hle => hlag y hy hdiv hle)
  · have := Nat.mod_lt g (show L.block > 0 by omega)
    simp only [Finset.mem_range, CtaBarrier.warps, hb]
    omega
  · intro y j pc' cnt' m _ _ _ hj hord
    exact Bar.bar0_count_none hX hS ht hj (by omega)

/-- **A blocked `bar.sync 0, 128` of the loop steps**, given the `time` facts of the loop
warps' lanes and the agreement of the default partition's threads on the count of each ordinal
(`Bar.AlphaAgree`, an open row of thread-layer gaps). -/
theorem bar0_loop_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hmax : Maximal L kernel asms mem0 X)
    (ht : Frame.Tracked (code L Q) X) (hA : Bar.AlphaAgree L X) {g pc : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) 0 (some 128) pc) {d : TSt}
    (hd : St Q L X g ((X.tr g).length - 1) = some (some d))
    (hafter : (∃ d', St Q L X g ((X.tr g).length - 1 + 1) = some (some d') ∧ T g d < T g d') ∨
      St Q L X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block → y % L.block < 128 →
      (X.tr y).countP (Execution.isBarId 0) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hcls := Bar.bar0_sources hpre hX hS ht
  have hgD : g % L.block < 128 := by
    rcases Interface.bar0_event_class hpre hX hS ht (show X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .bar 0 (some 128) .sync⟩ from hlast) with h | ⟨-, h, -⟩
    · cases h
    · exact h
  have hwD : ∀ {t : Nat}, t % L.block < 128 → t % L.block / 32 ∈ Bar.loopGroup := by
    intro t h
    simp only [Bar.loopGroup, Finset.mem_range]
    omega
  refine bar_steps_phased (Bar.loopGroup_sub hpre) Bar.loopGroup_card (Bar.loopGroup_ne hpre)
    Bar.loopGroup_target hcls (bar0_loop_shape hpre) hs hmax hp hnr hlen hlast (hwD hgD)
    (fun w hw => .inl hw) ?_ hd hafter (fun y hy hdiv hyp hle => hlag y hy hdiv ?_ hle)
  · intro y j pc' cnt' m hy hdiv hyp hj hord
    have hyD : y % L.block < 128 := by
      simp only [Bar.loopGroup, Finset.mem_range] at hyp
      omega
    exact (hA hy hg hdiv hyD hgD hj (show X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .bar 0 (some 128) .sync⟩ from hlast) hord).symm ▸ rfl
  · simp only [Bar.loopGroup, Finset.mem_range] at hyp
    omega

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
