-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Bar
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Step.CtaBarAppendWarp
public import Lemmas.Quiet.Step.CtaBarFinishExit

@[expose] public section

/-! # Named-barrier steps under quiet extensions

`Lemmas/Kernel/Progress/Bar.lean` under `Assumption.WfQuiet`. -/

namespace PTX.Sched
open PTX
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **Progress at a `bar.sync` whose generation is not done**, given the barrier's group and
the lag of a participant that has not made its arrival of the thread's ordinal. -/
theorem bar_sync_stepsQ (hwf : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hfault : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) (hmax : Maximal L K A mem0 X)
    {g : Nat} (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) {id pc : Nat}
    {cnt : Option Nat} (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id cnt pc)
    {p : Finset Nat} (hG : NamedBar.Shape L cnt p id) (hS : NamedBar.Sources L X cnt p id)
    (hlag : ∀ y, y < L.block → y / 32 ∈ p →
      (X.tr (g / L.block * L.block + y)).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) →
      (∀ k pc, X.get (g / L.block * L.block + y, k) ≠ some ⟨pc, .exit⟩) ∧
        threadTime M X (g / L.block * L.block + y) < threadTime M X g) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc := NamedBar.cta_lt hg
  by_cases hA : ∃ y, y < L.block ∧ y / 32 ∈ p ∧
      (X.tr (g / L.block * L.block + y)).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)
  · obtain ⟨y, hy, hyp, hle⟩ := hA
    have hyt := NamedBar.cta_thread_lt hc hy
    have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
    obtain ⟨hnx, hlt⟩ := hlag y hy hyp hle
    exact earlier_steps hmax hnr (pending_of_noExit hX hg hne hyt (by rw [hdiv]) hnx) hlt
  · push Not at hA
    obtain ⟨Y, hY, htr, hrel⟩ := NamedBar.sync_releaseQ hmax hwf hfault hG hS hg hlast
      (fun y hy hyp => by
        obtain ⟨j, ev, hj, hq, hjo⟩ :=
          NamedBar.exists_ordinal (Execution.isBarId id) _ (hA y hy hyp)
        obtain ⟨pcj, cntj, mj, rfl⟩ := NamedBar.isBarId_form hq
        have hget : X.get (g / L.block * L.block + y, j) = some ⟨pcj, .bar id cntj mj⟩ := hj
        have hcj := (hS (_, j) pcj cntj ⟨mj, hget⟩ (NamedBar.cta_thread_lt hc hy)).2
        subst hcj
        exact ⟨j, pcj, mj, hget, hjo⟩)
    exact same_trace_steps hp hne hnr hY htr hrel

/-- **Progress at an unrecorded `bar.arrive`**, given the barrier's group and the lag of a lane
of the warp that has not made its event of the thread's ordinal. -/
theorem bar_arrive_stepsQ (hwf : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hfault : ¬ CtaBarFault L X) (hmax : Maximal L K A mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hw : ArriveWait L X g)
    {pc id : Nat} {cnt : Option Nat}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt .arrive⟩)
    {p : Finset Nat} (hG : NamedBar.Shape L cnt p id) (hS : NamedBar.Sources L X cnt p id)
    (hlag : ∀ y, y < L.block → y / 32 = g % L.block / 32 →
      (X.tr (g / L.block * L.block + y)).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) →
      (∀ k pc, X.get (g / L.block * L.block + y, k) ≠ some ⟨pc, .exit⟩) ∧
        threadTime M X (g / L.block * L.block + y) < threadTime M X g) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨pc', id', cnt', hlast', hnrec⟩ := hw
  rw [hlast] at hlast'
  obtain ⟨rfl, rfl, rfl⟩ : pc = pc' ∧ id = id' ∧ cnt = cnt' := by
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hlast'
    exact ⟨hlast'.1, hlast'.2.1, hlast'.2.2.1⟩
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hlast
    simp only at this
    omega
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc := NamedBar.cta_lt hg
  by_cases hA : ∃ y, y < L.block ∧ y / 32 = g % L.block / 32 ∧
      (X.tr (g / L.block * L.block + y)).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)
  · obtain ⟨y, hy, hyw, hle⟩ := hA
    have hyt := NamedBar.cta_thread_lt hc hy
    obtain ⟨hdiv, hmod⟩ := NamedBar.lane_cta (c := g / L.block) hb hy
    have hsw : SameWarp L g (g / L.block * L.block + y) :=
      ⟨⟨hg, hyt, hdiv.symm⟩, by rw [hmod, hyw]⟩
    obtain ⟨hnx, hlt⟩ := hlag y hy hyw hle
    exact earlier_steps hmax hnr (pending_of_noExit hX hg hne hyt (cluster_of_sameWarp hsw) hnx)
      hlt
  · push Not at hA
    obtain ⟨Y, hY, htr, hrec⟩ := NamedBar.arrive_releaseQ hmax hwf hfault hg hG.id_lt hG.target
      hlast hnrec (fun y hy hyw => by
        obtain ⟨j, ev, hj, hq, hjo⟩ :=
          NamedBar.exists_ordinal (Execution.isBarId id) _ (hA y hy hyw)
        obtain ⟨pcj, cntj, mj, rfl⟩ := NamedBar.isBarId_form hq
        have hget : X.get (g / L.block * L.block + y, j) = some ⟨pcj, .bar id cntj mj⟩ := hj
        have hcj := (hS (_, j) pcj cntj ⟨mj, hget⟩ (NamedBar.cta_thread_lt hc hy)).2
        subst hcj
        exact ⟨j, pcj, mj, hget, hjo⟩)
    exact same_trace_steps hp hne hnr hY htr (released_of_arrive hY.1 htr hg hlast hrec)

end

end PTX.Sched
