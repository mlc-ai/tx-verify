-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.BarGroupU
public import Lemmas.Kernel.Progress.BarFinal

@[expose] public section

/-! # Progress at a named barrier whose history has several groups

A proof tool, generic over the kernel (promoted from Inkling's `Proof/Progress/WfBarSteps.lean`
and `WfBarFinal.lean`). A barrier whose arrivals follow `NamedBar.PhSources` (a loop group of
count `cD` and warps `D`, other arrivals without a count) steps a blocked `bar.sync` of

* a generation whose participants are loop warps, or whose source ordinal is below `start`
  (`Sched.barPhased_sync_stepsU`), given the lag of every participant lane that has made no more
  events on the barrier than the thread before its event, and
* the last generation, joined by every lane of the CTA without a count
  (`Sched.barFinal_sync_stepsU`), given the lag of every lane without a last-generation arrival. -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} [Fact K.NoBarArrive]

omit [Fact K.NoBarArrive] in
/-- **A blocked `bar.sync` of a barrier with one group steps**, given the group and the lag of its
participant lanes, for the event of the thread alone (`Sched.barGroup_sync_stepsU` asks the
group of every named-barrier event). -/
theorem barSingle_sync_stepsU (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hC : ∀ g < L.threads, (M.code g).SoundU) (hs : SafeGoal K A L mem0)
    {id : Nat} {count : Option Nat} {p : Finset Nat} (hG : NamedBar.Shape L count p id)
    (hS : NamedBar.Sources L X count p id)
    (htr : Frame.Tracked M.code X) (hmax : Maximal L K A mem0 X) {g pc : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hafter : ∀ {d : (M.code g).D},
      Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d) →
      (∃ d', Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = some (some d') ∧
        M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block → y % L.block / 32 ∈ p →
      (X.tr y).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) →
      ∀ {d : (M.code g).D}, Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨d, hd⟩ := Frame.state_of_noUbU hC hX htr (safe_noUb (hs.2 X hX)) hlast
  have hgt : M.time g d < threadTime M X g := threadTime_after hlen hd (hafter hd)
  refine bar_sync_steps hwf (fun Y hY => barFault_unsafe hs hY) hmax hp hnr hlen hlast
    hG hS fun y hy hyp hle => ?_
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  obtain ⟨hdiv, hmod⟩ := NamedBar.lane_cta (c := g / L.block) hb hy
  obtain ⟨hnx, hlt⟩ := hlag _ (NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy) hdiv
    (by rw [hmod]; exact hyp) hle hd
  exact ⟨hnx, by omega⟩

/-- **A blocked `bar.sync` of a phased barrier steps** when its group is the loop group or its
ordinal is below `start`. -/
theorem barPhased_sync_stepsU (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hC : ∀ g < L.threads, (M.code g).SoundU) (hs : SafeGoal K A L mem0)
    {D : Finset Nat} {cD : Option Nat} {start nD : Nat}
    (hD : D ⊆ Finset.range (CtaBarrier.warps L.block)) (hcard : D.card = nD)
    (hnD : nD ≠ CtaBarrier.warps L.block) (hcD : CtaBarrier.target L.block cD = .ok nD)
    {id : Nat} (hS : NamedBar.PhSources L X D cD start id) {count : Option Nat}
    {p : Finset Nat} (hG : NamedBar.Shape L count p id)
    (htr : Frame.Tracked M.code X) (hmax : Maximal L K A mem0 X) {g pc : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hgp : g % L.block / 32 ∈ p)
    (hgw : ∀ w ∈ p, w ∈ D ∨
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) < start)
    (hcnt : ∀ y j pc' cnt' m, y < L.threads → y / L.block = g / L.block →
      y % L.block / 32 ∈ p → X.get (y, j) = some ⟨pc', .bar id cnt' m⟩ →
      ((X.tr y).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) → cnt' = count)
    (hafter : ∀ {d : (M.code g).D},
      Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d) →
      (∃ d', Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = some (some d') ∧
        M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block → y % L.block / 32 ∈ p →
      (X.tr y).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) →
      ∀ {d : (M.code g).D}, Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc := NamedBar.cta_lt hg
  obtain ⟨d, hd⟩ := Frame.state_of_noUbU hC hX htr (safe_noUb (hs.2 X hX)) hlast
  have hgt : M.time g d < threadTime M X g := threadTime_after hlen hd (hafter hd)
  by_cases hA : ∃ y, y < L.block ∧ y / 32 ∈ p ∧
      (X.tr (g / L.block * L.block + y)).countP (Execution.isBarId id) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)
  · obtain ⟨y, hy, hyp, hle⟩ := hA
    have hyt := NamedBar.cta_thread_lt hc hy
    have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
    have hmod := (NamedBar.lane_cta (c := g / L.block) hb hy).2
    obtain ⟨hnx, hlt⟩ := hlag _ hyt hdiv (by rw [hmod]; exact hyp) hle hd
    exact earlier_steps hmax hnr (pending_of_noExit hX hg hne hyt (by rw [hdiv]) hnx) (by omega)
  · push Not at hA
    obtain ⟨Y, hY, htr', hrel⟩ := NamedBar.sync_release_phased hmax hwf
      (fun Y hY => barFault_unsafe hs hY) hD hcard hnD hcD hS hG hg hgp hlast hgw
      (fun y hy hyp => by
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
    exact same_trace_steps hp hne hnr hY htr' hrel

/-- A last-generation arrival of thread `y`: a `bar.sync` on `id` without a count whose source
ordinal is at least `start`. -/
def BarFinalArr (X : Execution) (id start y j : Nat) : Prop :=
  ∃ pc m, X.get (y, j) = some ⟨pc, .bar id none m⟩ ∧
    start ≤ ((X.tr y).take j).countP (Execution.isBarId id)

open Classical in
/-- **A blocked `bar.sync` of the last generation steps.** -/
theorem barFinal_sync_stepsU (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hC : ∀ g < L.threads, (M.code g).SoundU) (hs : SafeGoal K A L mem0)
    {D : Finset Nat} {cD : Option Nat} {start nD id : Nat}
    (hD : D ⊆ Finset.range (CtaBarrier.warps L.block)) (hcard : D.card = nD)
    (hnD : nD ≠ CtaBarrier.warps L.block) (hcD : CtaBarrier.target L.block cD = .ok nD)
    (hS : NamedBar.PhSources L X D cD start id)
    (hG : NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) id)
    (htr : Frame.Tracked M.code X) (hmax : Maximal L K A mem0 X) {g pc : Nat}
    (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g) (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id none pc)
    (hstartG : start ≤ ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id))
    (hone : ∀ j, BarFinalArr X id start g j → j = (X.tr g).length - 1)
    (hlock : ∀ y y' j j', y < L.threads → y' < L.threads → y / L.block = g / L.block →
      y' / L.block = g / L.block → y % L.block / 32 = y' % L.block / 32 →
      BarFinalArr X id start y j → BarFinalArr X id start y' j' →
      ((X.tr y).take j).countP (Execution.isBarId id) =
        ((X.tr y').take j').countP (Execution.isBarId id))
    (hafter : ∀ {d : (M.code g).D},
      Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d) →
      (∃ d', Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = some (some d') ∧
        M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g ((X.tr g).length - 1 + 1) = none)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block → (∀ j, ¬ BarFinalArr X id start y j) →
      ∀ {d : (M.code g).D}, Frame.stateAt M.code X g ((X.tr g).length - 1) = some (some d) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlen
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc := NamedBar.cta_lt hg
  obtain ⟨d, hd⟩ := Frame.state_of_noUbU hC hX htr (safe_noUb (hs.2 X hX)) hlast
  have hgt : M.time g d < threadTime M X g := threadTime_after hlen hd (hafter hd)
  by_cases hA : ∃ y, y < L.block ∧ ∀ j, ¬ BarFinalArr X id start (g / L.block * L.block + y) j
  · obtain ⟨y, hy, hno⟩ := hA
    have hyt := NamedBar.cta_thread_lt hc hy
    have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
    obtain ⟨hnx, hlt⟩ := hlag _ hyt hdiv hno hd
    exact earlier_steps hmax hnr (pending_of_noExit hX hg hne hyt (by rw [hdiv]) hnx) (by omega)
  · push Not at hA
    -- every lane has a last-generation arrival; the lanes of a warp agree on its ordinal
    let Gw : Nat → Nat := fun w =>
      if h : ∃ j, BarFinalArr X id start (g / L.block * L.block + w * 32) j then
        ((X.tr (g / L.block * L.block + w * 32)).take h.choose).countP (Execution.isBarId id)
      else 0
    have hlane : ∀ y, y < L.block → ∃ j pc m,
        X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id none m⟩ ∧
        ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) =
          Gw (y / 32) := by
      intro y hy
      obtain ⟨j, hj⟩ := hA y hy
      have hr : y / 32 * 32 < L.block := by omega
      have hex : ∃ j', BarFinalArr X id start (g / L.block * L.block + y / 32 * 32) j' := hA _ hr
      obtain ⟨pcj, mj, hget, hord0⟩ := hj
      refine ⟨j, pcj, mj, hget, ?_⟩
      have hGw : Gw (y / 32) = ((X.tr (g / L.block * L.block + y / 32 * 32)).take
          hex.choose).countP (Execution.isBarId id) := by
        simp only [Gw, hex, ↓reduceDIte]
      rw [hGw]
      have hyt := NamedBar.cta_thread_lt hc hy
      have hrt := NamedBar.cta_thread_lt hc hr
      have hdiv := (NamedBar.lane_cta (c := g / L.block) hb hy).1
      have hdivr := (NamedBar.lane_cta (c := g / L.block) hb hr).1
      have hmod := (NamedBar.lane_cta (c := g / L.block) hb hy).2
      have hmodr := (NamedBar.lane_cta (c := g / L.block) hb hr).2
      exact hlock _ _ _ _ hyt hrt hdiv hdivr (by rw [hmod, hmodr]; omega) ⟨pcj, mj, hget, hord0⟩
        hex.choose_spec
    have hgl : g % L.block < L.block := Nat.mod_lt _ hb
    have hgeq : g / L.block * L.block + g % L.block = g := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod g L.block
    have hFg : BarFinalArr X id start g ((X.tr g).length - 1) := ⟨pc, .sync, hlast, hstartG⟩
    have hGg : Gw (g % L.block / 32) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) := by
      have hr : g % L.block / 32 * 32 < L.block := by omega
      have hex : ∃ j', BarFinalArr X id start (g / L.block * L.block + g % L.block / 32 * 32) j' :=
        hA _ hr
      have hGw : Gw (g % L.block / 32) =
          ((X.tr (g / L.block * L.block + g % L.block / 32 * 32)).take
            hex.choose).countP (Execution.isBarId id) := by
        simp only [Gw, hex, ↓reduceDIte]
      rw [hGw]
      have hrt := NamedBar.cta_thread_lt hc hr
      have hdivr := (NamedBar.lane_cta (c := g / L.block) hb hr).1
      have hmodr := (NamedBar.lane_cta (c := g / L.block) hb hr).2
      exact hlock _ _ _ _ hrt hg hdivr rfl (by rw [hmodr]; omega) hex.choose_spec hFg
    have hstart : ∀ w ∈ Finset.range (CtaBarrier.warps L.block), start ≤ Gw w := by
      intro w hw
      have hwb := hG.bound w hw
      have hr : w * 32 < L.block := by omega
      have hex : ∃ j', BarFinalArr X id start (g / L.block * L.block + w * 32) j' := hA _ hr
      have hGw : Gw w = ((X.tr (g / L.block * L.block + w * 32)).take
          hex.choose).countP (Execution.isBarId id) := by
        simp only [Gw, hex, ↓reduceDIte]
      rw [hGw]
      obtain ⟨-, -, -, h2⟩ := hex.choose_spec
      exact h2
    obtain ⟨Y, hY, htr, hrel⟩ := NamedBar.sync_release_final hmax hwf
      (fun Y hY => barFault_unsafe hs hY) hD hcard hnD hcD hS hG hg hlast hGg hstart hlane
      (fun j pc' m h1 h2 => hone j ⟨pc', m, h1, h2⟩)
    exact same_trace_steps hp hne hnr hY htr hrel


end

end PTX.Sched
