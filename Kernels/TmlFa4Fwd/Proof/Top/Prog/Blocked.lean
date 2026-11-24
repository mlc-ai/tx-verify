-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Entry
public import Kernels.TmlFa4Fwd.Proof.Top.Register
public import Lemmas.Flow.NotAsyncWait
public import Lemmas.Flow.NotClc
public import Lemmas.Kernel.Progress.Reg
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcTime
import Kernels.TmlFa4Fwd.Proof.Lib.NoTc
import Kernels.TmlFa4Fwd.Proof.Mma.Export.TcTime
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Times
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TcTime
import Kernels.TmlFa4Fwd.Proof.Top.Prog.RegTime
import Kernels.TmlFa4Fwd.Proof.Top.Prog.TmemBulk
import Lemmas.Flow.NotBulk
import Lemmas.Kernel.Progress.BarGroup
import Lemmas.Kernel.Progress.TcColl
import Std.Tactic.BVDecide.Normalize.Prop

import Lemmas.Kernel.Progress.BarGroupU
import Lemmas.Kernel.Progress.TcCollU

@[expose] public section

/-! # A blocked pending lane steps

`Prog.blocked` proves this progress class, given safety (`SafeGoal`, rule P3: progress reads
safety only through it).

A pending lane that is not released is blocked by its last event (`Sched.thread_cases`). The
kernel has no cluster-barrier operation and no `cp.async.wait_group` (`kernel_noCluster`,
`kernel_noAsyncWait`, checked on the code), so the event is one of five kinds, each stepped by a
library template (`Lemmas/Kernel/Progress/`):

* a register request (`Sched.reg_steps`), from the requests' matching (`regMatch`: every request
  is its thread's first, at its warp's role entry, with its warpgroup's count) and every exit
  following a request (`regExit`: a role state follows its role's first state, which fires the
  request; `Prog/Entry.lean`), and the requests' time `scanBase` (`Prog/RegTime.lean`);
* a warp-collective `tcgen05` event (`Sched.tc_steps`), from the time table (`Times.tcLag`,
  `tcAfter`);
* a `bar.sync` or an unrecorded `bar.arrive` (`Sched.barGroup_sync_steps`, `barGroup_arrive_steps`),
  from the barriers' participant groups (`BarGroups`, `blocked_groups`) and the time table
  (`Times.barAfter`, `barLagWarp`: `bar_after`, `bar_lag`);
* a Tensor Memory resource operation (`tmem_steps`) and a bulk-group wait (`bulk_steps`),
  in `Prog/TmemBulk.lean`.

The time-table facts (`Times`, `blocked_times`) are facts of single threads' states, one per
kind. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- The code has no `cp.async.wait_group`. -/
theorem kernel_noAsyncWait : kernel.code.all (fun ins => !Flow.asyncWaitOp ins.op) = true := by
  decide +kernel

/-- **The time table's facts for the blocked kinds**: after a warp-collective
`tcgen05` event or a named-barrier event a lane is later or stopped; a lane of the warp that has
made no more such events is no later than the lane's state before its event. -/
structure Prog.Blocked.Times (p : Params) (L : Launch) (X : Execution) : Prop where
  tcLag : ∀ {g h j k : Nat} {d : (thread p L g).D}, g < L.threads → h < L.threads →
    SameWarp L g h → X.TcK (g, j) k → Frame.stateAt (thread p L) X g j = some (some d) →
    (X.tr h).countP isTcColl ≤ k →
    Sched.threadTime (Progress.timed p L) X h ≤ Progress.time p L g d
  tcAfter : ∀ {g j k : Nat} {d : (thread p L g).D}, g < L.threads → X.TcK (g, j) k →
    Frame.stateAt (thread p L) X g j = some (some d) →
    (∃ d', Frame.stateAt (thread p L) X g (j + 1) = some (some d') ∧
      Progress.time p L g d < Progress.time p L g d') ∨
      Frame.stateAt (thread p L) X g (j + 1) = none
  barAfter : ∀ {g j pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : (thread p L g).D},
    g < L.threads → X.get (g, j) = some ⟨pc, .bar id cnt md⟩ →
    Frame.stateAt (thread p L) X g j = some (some d) →
    (∃ d', Frame.stateAt (thread p L) X g (j + 1) = some (some d') ∧
      Progress.time p L g d < Progress.time p L g d') ∨
      Frame.stateAt (thread p L) X g (j + 1) = none
  barLagWarp : ∀ {g y j pc id : Nat} {cnt : Option Nat} {md : BarMode} {d : (thread p L g).D},
    g < L.threads → y < L.threads → SameWarp L g y →
    X.get (g, j) = some ⟨pc, .bar id cnt md⟩ → Frame.stateAt (thread p L) X g j = some (some d) →
    (X.tr y).countP (Execution.isBarId id) ≤ ((X.tr g).take j).countP (Execution.isBarId id) →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
        Sched.threadTime (Progress.timed p L) X y ≤ Progress.time p L g d

/-- **The named barriers' participant groups**, with the lag of a participant lane before a
`bar.sync`. -/
def Prog.Blocked.BarGroups (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∃ G : Nat → Nat → Prop,
    (∀ {g i pc id : Nat} {cnt : Option Nat} {md : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt md⟩ →
      ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id ∧
        ∀ w ∈ q, G id w) ∧
    ∀ {g y j pc id : Nat} {cnt : Option Nat} {d : (thread p L g).D},
      g < L.threads → y < L.threads → y / L.block = g / L.block → G id (y % L.block / 32) →
      X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩ →
      Frame.stateAt (thread p L) X g j = some (some d) →
      (X.tr y).countP (Execution.isBarId id) ≤ ((X.tr g).take j).countP (Execution.isBarId id) →
        (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
          Sched.threadTime (Progress.timed p L) X y ≤ Progress.time p L g d

/-- **The named barriers' participant groups**, with the lag of a participant lane. -/
theorem blocked_groups (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : Prog.Blocked.BarGroups p L X :=
  ⟨barGroup, fun _ he => bar_group hp hX (launchFollow hp hX) he,
    fun _ hy hc hG he hσ hle =>
      bar_lag hp hX (launchFollow hp hX) (Sched.safe_noUb (hs.2 X hX)) he hσ hy hc
        (.inl ⟨rfl, hG⟩) hle⟩

/-- **The time table's facts**: the softmax and correction warps' `tcgen05` events (`soft_tcLag`,
`corr_tcLag`), the MMA warp's resource events (`mma_tcLag`, `tc_next`); the output and loader warps
have no `tcgen05` event. -/
theorem blocked_times (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) :
    Prog.Blocked.Times p L X := by
  have hX := hmax.1
  have hub := Sched.safe_noUb (hs.2 X hX)
  have hFw := launchFollow hp hX
  have hno : ∀ {g j k : Nat}, 13 ≤ Prologue.warpIndex L g → ¬ X.TcK (g, j) k := by
    rintro g j k hw ⟨⟨e, he, hcl⟩, -⟩
    rw [noTc_of_warp hp hX hFw hw he] at hcl
    cases hcl
  refine ⟨fun {g h j k d} hg hh hsw hK hσ hle => ?_, fun {g j k d} hg hK hσ => ?_,
    fun _ he hσ => .inl (bar_after hp hX hFw hub he hσ), fun _ hy hsw he hσ hle =>
      bar_lag hp hX hFw hub he hσ hy hsw.1.2.2.symm (.inr hsw.2.symm) hle⟩
  · rcases Nat.lt_or_ge (Prologue.warpIndex L g) 12 with h1 | h1
    · rcases Nat.lt_or_ge (Prologue.warpIndex L g) 8 with h8 | h8
      · exact soft_tcLag hp hX hFw hub h8 hg hsw hK hσ hle
      · exact corr_tcLag hp hX hFw hub h8 (by omega) hg hsw hK hσ hle
    rcases Nat.lt_or_ge (Prologue.warpIndex L g) 13 with h2 | h2
    · exact Mma.mma_tcLag hp hX hub hg (by omega) hFw hsw hK hσ hle
    · exact (hno h2 hK).elim
  · rcases Nat.lt_or_ge (Prologue.warpIndex L g) 12 with h1 | h1
    · have htr : Frame.Tracked (thread p L) X := fun h k hh => (goodR' hp hX hh k).1
      rcases Nat.lt_or_ge (Prologue.warpIndex L g) 8 with h8 | h8
      · exact soft_tcAfter hp hX hFw hub h8 hg htr hK hσ
      · exact corr_tcAfter hp hX hFw hub h8 (by omega) hg htr hK hσ
    rcases Nat.lt_or_ge (Prologue.warpIndex L g) 13 with h2 | h2
    · left
      obtain ⟨⟨e, he, hcl⟩, -⟩ := hK
      have hne : ∀ f, e.kind ≠ .ub f := fun f hf => by
        obtain ⟨pc, kd⟩ := e
        simp only at hf
        subst hf
        cases hcl
      obtain ⟨σ', hn, ht⟩ := Mma.tc_next ((Mma.mma_tc_ev hp hX (by omega) hFw he hne hσ).2 hcl) e
      refine ⟨σ', ?_, ht⟩
      rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[j]? = some e from he), hσ]
      exact hn
    · exact (hno h2 hK).elim

/-- **A blocked pending lane steps**, for every consistent execution. -/
theorem Prog.blocked (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    ∀ X, Maximal L kernel Assumptions.all m X → ∀ g, Frame.Pending L X g →
      ¬ Step.Released L X g → StepsAt p L m X (.thread g) := by
  intro X hmax g hpd hrel
  have hX := hmax.1
  have hC : ∀ g < L.threads, ((Progress.timed p L).code g).SoundU :=
    fun g hg => thread_sound hp hg
  have htr : Frame.Tracked (Progress.timed p L).code X :=
    fun h k hh => (goodR' hp hX hh k).1
  have hwf : Assumption.WfStep (fun _ => true) L kernel m Assumptions.all :=
    fun X Y hX hle hord hr =>
      Assumptions.wfStep X Y hX hle (fun e r h1 h2 j pc sp hj _ hlt hno =>
        hord e r h1 h2 j pc sp hj rfl hlt hno) hr
  have hna : ∀ pc n, X.get (g, (X.tr g).length - 1) ≠ some ⟨pc, .asyncWait n⟩ :=
    fun pc n he => Flow.no_kind_of_code hX Flow.asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
      (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => Flow.fires_asyncWait_op hf hk)
      kernel_noAsyncWait he ⟨n, rfl⟩
  obtain ⟨G, hgroup, hlagS⟩ := blocked_groups hp hs hX
  have hT := blocked_times hp hs hmax
  have hmatch : Sched.RegMatch L X := regMatch hp hX
  have hexit : Sched.RegExit L X := regExit hp hX
  rcases Sched.thread_cases hX hpd.1 hna hrel with h | h | h | h | h | h | h
  · exfalso
    obtain ⟨pc, op, he, -⟩ := h
    exact Flow.no_kind_of_code hX Flow.clusterOp (fun k => ∃ op, k = .cluster op)
      (fun _ ⟨_, h⟩ => by cases h)
      (fun hf ⟨_, hk⟩ => by rw [Flow.fires_cluster_op hf hk]; rfl) kernel_noCluster he ⟨op, rfl⟩
  · exact Sched.reg_steps hs hmatch hexit (by rw [hp.block])
      (fun hh hno => reg_before hp hX (Sched.safe_noUb (hs.2 X hX)) hh hno) (fun hg he =>
          reg_after hp hX hg he) hmax hpd
      hrel h
  · exact tmem_steps hp hs hmax (fun hpd hrel h =>
      Sched.tc_stepsU hC hs htr hT.tcLag hT.tcAfter hmax hpd hrel h) hpd hrel h
  · exact Sched.barGroup_sync_stepsU hwf hC hs hgroup hT.barAfter hlagS htr hmax hpd hrel h
  · exact Sched.tc_stepsU hC hs htr hT.tcLag hT.tcAfter hmax hpd hrel h
  · exact Sched.barGroup_arrive_stepsU hwf hC hs hgroup hT.barAfter hT.barLagWarp htr hmax hpd
      hrel h
  · exact bulk_steps hmax hrel h

end PTX.Kernels.TmlFa4Fwd.Proof.Top
