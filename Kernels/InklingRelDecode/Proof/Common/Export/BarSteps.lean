-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.Export.BarClock
import Kernels.InklingRelDecode.Proof.Common.Export.BarAfter
import Kernels.InklingRelDecode.Proof.Common.Export.BarEarly
import Kernels.InklingRelDecode.Proof.Common.Export.BarFinal
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Kernel.Progress.BarPhasedSteps

@[expose] public section

/-! # A lane blocked at a rendezvous of a named barrier steps

The clock facts of the barriers (`bar1_after`, `bar0_after`, `bar1_lag`) in the form the
progress tools ask for. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Sched

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The clock rises after a recorded barrier event, or the lane stops. -/
private theorem after_of {j} (hf : Follow Q L X) (hg : g < L.threads)
    (h : timeAt (schedule Q L) X g j < timeAt (schedule Q L) X g (j + 1)) {d}
    (hd : Frame.stateAt (schedule Q L).code X g j = some (some d)) :
    (∃ d', Frame.stateAt (schedule Q L).code X g (j + 1) = some (some d') ∧
      (schedule Q L).time g d < (schedule Q L).time g d') ∨
      Frame.stateAt (schedule Q L).code X g (j + 1) = none := by
  rcases h1 : Frame.stateAt (thread Q L) X g (j + 1) with _ | _ | d'
  · exact .inr h1
  · exact absurd h1 ((hf g hg (j + 1)).1)
  · refine .inl ⟨d', h1, ?_⟩
    have e0 : timeAt (schedule Q L) X g j = (schedule Q L).time g d := time_at hd
    have e1 : timeAt (schedule Q L) X g (j + 1) = (schedule Q L).time g d' := time_at h1
    omega

/-- **A lane blocked at a rendezvous of barrier 1 steps**, given the group of the barrier: the
whole CTA arrives at the clock of the generation, and the lanes with fewer events are earlier. -/
public theorem bar1_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (nu : ∀ y, NoUbLane X y) {pc : Nat} {p : Finset Nat}
    (hG : NamedBar.Shape L none p 1) (hS : NamedBar.Sources L X none p 1)
    (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hlen : 0 < (X.tr g).length) (hlast : X.IsBarrier (g, (X.tr g).length - 1) 1 none pc) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar 1 none .sync⟩ := hlast
  refine Sched.barSingle_sync_stepsU (M := schedule Q L) Lib.assumptions_step
    (fun _ hg => thread_sound hp hg) hs hG hS (fun h k hh => (hf h hh k).1) hmax hpd hrel hlen
    hlast (fun {d} hd => ?_) (fun y hy hc hw hle {d} hd => ?_)
  · exact after_of hf hpd.1 (bar1_after hp hX hf words hget) hd
  · have := bar1_lag hp hX hf words hy (nu y) hget hle
    have e0 : timeAt (schedule Q L) X g ((X.tr g).length - 1) = (schedule Q L).time g d :=
      time_at hd
    exact ⟨this.1, this.2.trans e0.le⟩

/-- **A lane blocked at a startup rendezvous steps**, given the group of the barrier. -/
public theorem bar0_early_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X)
    (nu : ∀ y, NoUbLane X y) {D : Finset Nat} {cD : Option Nat} {nD : Nat}
    (hD : D ⊆ Finset.range (CtaBarrier.warps L.block)) (hcard : D.card = nD)
    (hnD : nD ≠ CtaBarrier.warps L.block) (hcD : CtaBarrier.target L.block cD = .ok nD)
    (hS : NamedBar.PhSources L X D cD 2 0) {p : Finset Nat} (hG : NamedBar.Shape L none p 0)
    {pc : Nat} (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hlen : 0 < (X.tr g).length) (hlast : X.IsBarrier (g, (X.tr g).length - 1) 0 none pc)
    (hgp : g % L.block / 32 ∈ p)
    (hcnt : ∀ y j pc' cnt' md, y < L.threads → y / L.block = g / L.block →
      y % L.block / 32 ∈ p → X.get (y, j) = some ⟨pc', .bar 0 cnt' md⟩ →
      ((X.tr y).take j).countP (Execution.isBarId 0) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) → cnt' = none)
    (hlt : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) < 2) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar 0 none .sync⟩ := hlast
  refine Sched.barPhased_sync_stepsU (M := schedule Q L) Lib.assumptions_step
    (fun _ hg => thread_sound hp hg) hs hD hcard hnD hcD hS hG (fun h k hh => (hf h hh k).1) hmax
    hpd hrel hlen hlast hgp (fun w _ => Or.inr hlt) hcnt (fun {d} hd => ?_)
    (fun y hy hc hw hle {d} hd => ?_)
  · exact after_of hf hpd.1 (bar0_after hp hX hf hget) hd
  · have := bar0_early_lag hp hX hf hget hlt hy (nu y) hle
    have e0 : timeAt (schedule Q L) X g ((X.tr g).length - 1) = (schedule Q L).time g d :=
      time_at hd
    exact ⟨this.1, this.2.trans e0.le⟩

/-- **A lane blocked at the last generation of barrier 0 steps**, given the group of the barrier
and that the lanes of a warp agree on the ordinal of their last-generation arrival. -/
public theorem bar0_final_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (nu : ∀ y, NoUbLane X y) {D : Finset Nat} {cD : Option Nat} {nD : Nat}
    (hD : D ⊆ Finset.range (CtaBarrier.warps L.block)) (hcard : D.card = nD)
    (hnD : nD ≠ CtaBarrier.warps L.block) (hcD : CtaBarrier.target L.block cD = .ok nD)
    (hS : NamedBar.PhSources L X D cD 2 0)
    (hG : NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) 0) {pc : Nat}
    (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hlen : 0 < (X.tr g).length) (hlast : X.IsBarrier (g, (X.tr g).length - 1) 0 none pc)
    (hord : 2 ≤ ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0))
    (hlock : ∀ y y' j j', y < L.threads → y' < L.threads → y / L.block = g / L.block →
      y' / L.block = g / L.block → y % L.block / 32 = y' % L.block / 32 →
      BarFinalArr X 0 2 y j → BarFinalArr X 0 2 y' j' →
      ((X.tr y).take j).countP (Execution.isBarId 0) =
        ((X.tr y').take j').countP (Execution.isBarId 0)) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar 0 none .sync⟩ := hlast
  refine Sched.barFinal_sync_stepsU (M := schedule Q L) Lib.assumptions_step
    (fun _ hg => thread_sound hp hg) hs hD hcard hnD hcD hS hG (fun h k hh => (hf h hh k).1) hmax
    hpd hrel hlen hlast hord (fun j h' => final_one hp hX hget hord h') hlock
    (fun {d} hd => ?_) (fun y hy hc hno {d} hd => ?_)
  · exact after_of hf hpd.1 (bar0_after hp hX hf hget) hd
  · have := bar0_final_lag hp hX hf words hget hord hy (nu y) hno
    have e0 : timeAt (schedule Q L) X g ((X.tr g).length - 1) = (schedule Q L).time g d :=
      time_at hd
    exact ⟨this.1, this.2.trans e0.le⟩

/-- **A lane blocked at a loop rendezvous of barrier 0 steps**, given the group of the barrier and
the lag of the data lanes with no more events. -/
public theorem bar0_loop_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X)
    {D : Finset Nat} {nD : Nat} (hD : D ⊆ Finset.range (CtaBarrier.warps L.block))
    (hcard : D.card = nD) (hnD : nD ≠ CtaBarrier.warps L.block)
    (hcD : CtaBarrier.target L.block (some 128) = .ok nD)
    (hS : NamedBar.PhSources L X D (some 128) 2 0) (hG : NamedBar.Shape L (some 128) D 0)
    {pc : Nat} (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hlen : 0 < (X.tr g).length)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) 0 (some 128) pc)
    (hgp : g % L.block / 32 ∈ D)
    (hcnt : ∀ y j pc' cnt' md, y < L.threads → y / L.block = g / L.block →
      y % L.block / 32 ∈ D → X.get (y, j) = some ⟨pc', .bar 0 cnt' md⟩ →
      ((X.tr y).take j).countP (Execution.isBarId 0) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) → cnt' = some 128)
    (hlag : ∀ y, y < L.threads → y / L.block = g / L.block → y % L.block / 32 ∈ D →
      (X.tr y).countP (Execution.isBarId 0) ≤
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
        threadTime (schedule Q L) X y ≤ timeAt (schedule Q L) X g ((X.tr g).length - 1)) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar 0 (some 128) .sync⟩ := hlast
  refine Sched.barPhased_sync_stepsU (M := schedule Q L) Lib.assumptions_step
    (fun _ hg => thread_sound hp hg) hs hD hcard hnD hcD hS hG (fun h k hh => (hf h hh k).1) hmax
    hpd hrel hlen hlast hgp (fun w hw => Or.inl hw) hcnt (fun {d} hd => ?_)
    (fun y hy hc hw hle {d} hd => ?_)
  · exact after_of hf hpd.1 (bar0_after hp hX hf hget) hd
  · have := hlag y hy hc hw hle
    have e0 : timeAt (schedule Q L) X g ((X.tr g).length - 1) = (schedule Q L).time g d :=
      time_at hd
    exact ⟨this.1, this.2.trans e0.le⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
