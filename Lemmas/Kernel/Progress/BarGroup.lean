-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Bar
public import Lemmas.Kernel.Goals
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # Progress at named barriers with participant groups

A proof tool, generic over the kernel (promoted from FA4's
`Proof/Progress/CollectiveBarGroup.lean`). A kernel whose every named-barrier event's barrier has
a group (`NamedBar.Shape`) whose arrivals are its warps' (`NamedBar.Sources`), with the group's
warps in a predicate `G id` (`hgroup`),
steps a blocked `bar.sync` (`Sched.barGroup_sync_steps`, through `Sched.bar_sync_steps`) and an
unrecorded `bar.arrive` (`Sched.barGroup_arrive_steps`, through `Sched.bar_arrive_steps`), given
its time table's facts: after a named-barrier event the thread is later, or its machine has
stopped (`hafter`); a participant lane (of the group for a `bar.sync`, of the thread's warp for a
`bar.arrive`) that has made no more events on the barrier than the thread before its event has not
exited and is no later than the thread's state before the event (`hlag_sync`, `hlag_warp`). -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- A CTA barrier fault makes a consistent execution unsafe. -/
theorem barFault_unsafe (hs : SafeGoal K A L mem0) {Y : Execution}
    (hY : Consistent L K A mem0 Y) : ¬ CtaBarFault L Y :=
  fun hf => hs.2 Y hY (by unfold Unsafe; simp [hf])

/-- **Progress at a blocked `bar.sync` of a barrier with a participant group.** -/
theorem barGroup_sync_steps (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
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
  refine bar_sync_steps hwf (fun Y hY => barFault_unsafe hs hY) hmax hp hnr hlen hlast
    hG hS fun y hy hyp hle => ?_
  obtain ⟨hdiv, hmod⟩ := NamedBar.lane_cta (c := g / L.block) hb hy
  obtain ⟨hnx, hlt⟩ := hlag_sync hg (NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy) hdiv
    (by rw [hmod]; exact hpg _ hyp) hlast hdb hle
  exact ⟨hnx, by omega⟩

/-- **Progress at an unrecorded `bar.arrive` of a barrier with a participant group.** -/
theorem barGroup_arrive_steps (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
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
    (hlag_warp : ∀ {g y j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : (M.code g).D},
      g < L.threads → y < L.threads → SameWarp L g y →
      X.get (g, j) = some ⟨pc, .bar id cnt m⟩ → Frame.stateAt M.code X g j = some (some d) →
      (X.tr y).countP (Execution.isBarId id) ≤ ((X.tr g).take j).countP (Execution.isBarId id) →
        (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d)
    (htr : Frame.Tracked M.code X) (hmax : Maximal L K A mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hw : ArriveWait L X g) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨pc, id, cnt, hlast, -⟩ := id hw
  have hlen : 0 < (X.tr g).length := by
    have := len_of_get hlast
    simp only at this
    omega
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  obtain ⟨p, hG, hS, -⟩ := hgroup hg hlast
  obtain ⟨db, hdb⟩ := Frame.state_of_noUb hC hX htr (safe_noUb (hs.2 X hX)) hlast
  have hgt : M.time g db < threadTime M X g :=
    threadTime_after hlen hdb (hafter hg hlast hdb)
  refine bar_arrive_steps hwf (barFault_unsafe hs hX) hmax hp hnr hw hlast hG hS
    fun y hy hyw hle => ?_
  have hyt := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy
  obtain ⟨hdiv, hmod⟩ := NamedBar.lane_cta (c := g / L.block) hb hy
  obtain ⟨hnx, hlt⟩ := hlag_warp hg hyt ⟨⟨hg, hyt, hdiv.symm⟩, by rw [hmod, hyw]⟩
    hlast hdb hle
  exact ⟨hnx, by omega⟩

end

end PTX.Sched
