-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Step.CtaBarFinishExit
public import Lemmas.Step.CtaBarAppendWarp

@[expose] public section

/-! # Progress at a named barrier

A pending thread whose last event is a named-barrier event that cannot return steps, given the
barrier's group (`NamedBar.Shape`, `NamedBar.Sources`: the arrivals on the barrier are its
participant warps') and the time of a participant that has not made its event of the thread's
ordinal (`hlag`: it has not exited and is earlier than the thread).

* **A `bar.sync` whose generation is not done** (`BarWait`, `bar_sync_steps`). A participant lane
  of the CTA that has made no more events on the barrier than the thread's ordinal `G` there is
  earlier (`earlier_steps`). Otherwise every participant has made its arrival of ordinal `G`, and
  a maximal execution with the same traces releases the thread (`NamedBar.sync_release`), in
  which it ranks one lower (`same_trace_steps`).
* **A `bar.arrive` without its record** (`ArriveWait`, `bar_arrive_steps`): it waits only for the
  lanes of its warp. A lane with no more events on the barrier is earlier; otherwise the warp's
  arrival record is appended (`NamedBar.arrive_release`), which releases the thread
  (`released_of_arrive`).

The extensions perform no commit arrive-on, so the assumptions keep their constraints (`hwf`);
an execution with a CTA barrier fault is excluded (`hfault`). -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- A thread whose last event leads from state `d` to a later state, or stops its machine, is
later than `d`. -/
theorem threadTime_after {g : Nat} {d : (M.code g).D} (hlen : 0 < (X.tr g).length)
    (hd : Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d))
    (ha : (∃ d', Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = some (some d') ∧
      M.time g d < M.time g d') ∨ Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = none) :
    M.time g d < threadTime M X g := by
  rw [Nat.sub_add_cancel hlen] at ha
  rcases ha with ⟨d', hd', hlt⟩ | hnone
  · rw [threadTime_of hd']
    exact hlt
  · rw [threadTime_stop hd hnone]
    omega

/-- A thread whose last event is a recorded `bar.arrive` is released: the arrival is ready
(`NamedBar.ready_of_arrivalK`). -/
theorem released_of_arrive {Y : Execution} (hY : Consistent L K A mem0 Y)
    (htr : Y.tr = X.tr) {g pc id : Nat} (hg : g < L.threads)
    {cnt : Option Nat} (hlast : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt .arrive⟩)
    (hrec : (g, (X.tr g).length - 1) ∈
      (Y.barriers (g / L.block)).flatMap CtaBarrier.Record.refs) :
    Step.Released L Y g := by
  have hlastY : Y.get (g, (Y.tr g).length - 1) = some ⟨pc, .bar id cnt .arrive⟩ := by
    simpa [Execution.get, htr] using hlast
  refine ⟨fun _ _ _ _ => ?_⟩
  obtain ⟨gen, hk⟩ := NamedBar.recorded_arrivalK hY hlastY hg (by simpa [htr] using hrec)
  exact NamedBar.ready_of_arrivalK hY.ctaBar hlastY hk

/-- **Progress at a `bar.sync` whose generation is not done**, given the barrier's group and
the lag of a participant that has not made its arrival of the thread's ordinal. -/
theorem bar_sync_steps (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
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
    obtain ⟨Y, hY, htr, hrel⟩ := NamedBar.sync_release hmax hwf hfault hG hS hg hlast
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
theorem bar_arrive_steps (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
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
    obtain ⟨Y, hY, htr, hrec⟩ := NamedBar.arrive_release hmax hwf hfault hg hG.id_lt hG.target
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
