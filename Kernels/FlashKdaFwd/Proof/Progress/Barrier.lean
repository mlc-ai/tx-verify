-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Progress.Wf
public import Lemmas.Kernel.Progress.BarGroup

@[expose] public section

/-!
# Progress at a blocked `bar.sync`, under a same-trace premise

Kernel-independent restatements of `Sched.bar_sync_steps` (`Lemmas/Kernel/Progress/Bar.lean`)
and `Sched.barGroup_sync_steps` (`Lemmas/Kernel/Progress/BarGroup.lean`). The originals take
`Assumption.WfStep`; they use it only to append records to a CTA barrier's history, an extension
with the same thread events. Here the premise is `WfSameTr` (`Wf.lean`), and the release of the
thread is the library's `NamedBar.sync_release_of_wf`, which asks exactly for the constraints of
such extensions (`Assumption.WfCtaHistory`).

A pending thread whose last event is a `bar.sync` whose generation is not done steps: a
participant lane that has made no more events on the barrier than the thread had made before
its arrival is a pending thread at an earlier time; otherwise every participant has arrived and
an execution with the same thread events releases the thread, in which it ranks one lower.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **Progress at a `bar.sync` whose generation is not done**, given the barrier's group and
the lag of a participant that has not made its arrival of the thread's ordinal. -/
theorem bar_sync_stepsE (hwf : WfSameTr L K mem0 A)
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
    obtain ⟨Y, hY, htr, hrel⟩ := NamedBar.sync_release_of_wf hmax hwf.ctaHistory hfault hG hS hg
      hlast (fun y hy hyp => by
        obtain ⟨j, ev, hj, hq, hjo⟩ :=
          NamedBar.exists_ordinal (Execution.isBarId id) _ (hA y hy hyp)
        obtain ⟨pcj, cntj, mj, rfl⟩ := NamedBar.isBarId_form hq
        have hget : X.get (g / L.block * L.block + y, j) = some ⟨pcj, .bar id cntj mj⟩ := hj
        have hcj := (hS (_, j) pcj cntj ⟨mj, hget⟩ (NamedBar.cta_thread_lt hc hy)).2
        subst hcj
        exact ⟨j, pcj, mj, hget, hjo⟩)
    exact same_trace_steps hp hne hnr hY htr hrel

/-- **Progress at a blocked `bar.sync` of a barrier with a participant group.** -/
theorem barGroup_sync_stepsE (hwf : WfSameTr L K mem0 A)
    (hC : ∀ g < L.threads, (M.code g).Sound) (hs : SafeGoal K A L mem0)
    {G : Nat → Nat → Prop}
    (hgroup : ∀ {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt m⟩ →
      ∃ p : Finset Nat, NamedBar.Shape L cnt p id ∧ NamedBar.Sources L X cnt p id ∧
        ∀ w ∈ p, G id w)
    (hafter : ∀ {g j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : (M.code g).D},
      g < L.threads → X.get (g, j) = some ⟨pc, .bar id cnt m⟩ →
      Frame.stateAt M.code X g j = some (some d) →
      (∃ d', Frame.stateAt M.code X g (j + 1) = some (some d') ∧ M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g (j + 1) = none)
    (hlag_sync : ∀ {g y j pc id : Nat} {cnt : Option Nat} {d : (M.code g).D},
      g < L.threads → y < L.threads → y / L.block = g / L.block → G id (y % L.block / 32) →
      X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩ → Frame.stateAt M.code X g j = some (some d) →
      (X.tr y).countP (Execution.isBarId id) ≤ ((X.tr g).take j).countP (Execution.isBarId id) →
        (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d)
    (htr : Frame.Tracked M.code X) (hmax : Maximal L K A mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hw : BarWait L X g) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  obtain ⟨id, cnt, pc, hlen, hlast, -⟩ := hw
  have hg := hp.1
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  obtain ⟨p, hG, hS, hpg⟩ := hgroup hg hlast
  obtain ⟨db, hdb⟩ := Frame.state_of_noUb hC hX htr (safe_noUb (hs.2 X hX)) hlast
  have hgt : M.time g db < threadTime M X g :=
    threadTime_after hlen hdb (hafter hg hlast hdb)
  refine bar_sync_stepsE hwf (fun Y hY => barFault_unsafe hs hY) hmax hp hnr hlen hlast
    hG hS fun y hy hyp hle => ?_
  obtain ⟨hdiv, hmod⟩ := NamedBar.lane_cta (c := g / L.block) hb hy
  obtain ⟨hnx, hlt⟩ := hlag_sync hg (NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy) hdiv
    (by rw [hmod]; exact hpg _ hyp) hlast hdb hle
  exact ⟨hnx, by omega⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
