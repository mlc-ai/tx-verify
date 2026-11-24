-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Tcgen05.TcCommit
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Order.OrderNotAccess

/-!
# Litmus tests for the tcgen05 fences (DEP-TC-FENCE)

The canonical synchronization patterns of PTX ISA 9.5 §9.7.18.6.4, with `.relaxed` mbarrier
operations, are ordered as the text says; removing a fence leaves them unordered.

* `P41` (4.1, pipelined, same thread): `tcgen05.cp` then an MMA reading A at the copied
  address is a pipelined pair by program order alone.
* `P42a` (4.2 Example 1): `tcgen05.st`, `tcgen05.wait::st`, `tcgen05.ld`: the store is
  ordered before the load.
* `P42b` (4.2 Example 2): MMA, commit, relaxed `try_wait`, `fence::after_thread_sync`, load:
  the MMA's completion is ordered before the load (`DoneBefore`), with no acquire.
  `P42bNoFence`: without the fence it is not.
* `P43` (4.3): `tcgen05.cp` in lane 0, `bar.warp.sync`, an MMA reading the copy in lane 1:
  a pipelined pair across threads of one warp. `P43Fenced`: the same pair ordered by
  `fence::before_thread_sync`, a relaxed arrive, a relaxed `try_wait` and
  `fence::after_thread_sync`.
* `P44a` (4.4 Example 1): load, `wait::ld`, `fence::before_thread_sync`, relaxed arrive;
  relaxed `try_wait`, `fence::after_thread_sync`, MMA in another thread: the load's
  completion is ordered before the MMA (`WaitBefore`). `P44aNoBefore` and
  `P44aNoAfter`: without either fence it is not.
* `P44b` (4.4 Example 2): MMA and commit in one thread; relaxed `try_wait`,
  `fence::after_thread_sync`, load in another: `DoneBefore`. `P44bNoFence`: without the
  fence it is not.
* `Composed` (the composed example of 4.4): MMA and commit to `bar1`; a second thread waits
  on `bar1` and arrives on `bar2`, relaxed; a third waits on `bar2`, fences and loads: the
  relay through the second thread is two observations and orders nothing
  (EXT-TC-EXEC-ORDER), so the MMA's completion is not ordered before the load.

Pattern 4.5 (register dependency) orders no memory access; the data flow of a thread (THREAD-RUN)
represents it (`Tests/Tc/TcLdOrder.lean`). -/

namespace PTX.Tests.TcFence
open PTX PTX.AsyncCopy

noncomputable section

private def replayLog (ops : List (Ref × MBarrier.Action)) : List (MBarrier.Record Ref) :=
  match MBarrier.replay none ops with
  | .ok xs => xs
  | .error _ => []

def launch (n : Nat) : Launch :=
  { grid := 1, block := n, params := fun _ => none, sharedBase := 0, clusterSize := 1 }
@[simp] def bar : Loc := ⟨.shared, 0, 0⟩
@[simp] def bar2 : Loc := ⟨.shared, 0, 8⟩
def src : TcShared.Descriptor := ⟨64, 0, 0, 0, false, false, .none⟩
def spec (aTmem : Option Nat) : TcMma.OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩, src, src, 0, 0, aTmem,
    {}⟩
@[simp] def mma : Event := ⟨1, .tc (.mma 0 (spec none) false [0, 0, 0, 0])⟩
/-- An MMA reading A from Tensor Memory column 0. -/
@[simp] def mmaA : Event := ⟨1, .tc (.mma 64 (spec (some 0)) false [0, 0, 0, 0])⟩
@[simp] def tld : Event := ⟨2, .tc (.ld 0 [] .s32x32b)⟩
@[simp] def waitLd : Event := ⟨3, .tc .waitLd⟩
@[simp] def commit (m : Loc) : Event := ⟨5, .tc (.commit (TcCommit.unicast m))⟩
/-- `mbarrier.try_wait.parity.relaxed.cluster`, successful. -/
@[simp] def pollR (m : Loc) : Event := ⟨6, .wait m 0 true false .cluster⟩
/-- `mbarrier.arrive.relaxed.cluster`. -/
@[simp] def arriveR (m : Loc) : Event := ⟨9, .arrive m 0 1 false .cluster⟩
@[simp] def init (m : Loc) : Event := ⟨7, .mbInit m 1⟩
@[simp] def fBefore : Event := ⟨10, .tc .fenceBefore⟩
@[simp] def fAfter : Event := ⟨11, .tc .fenceAfter⟩
@[simp] def cp : Event := ⟨12, .tc (.cp ⟨0, src, .s128x256b, [0], none⟩)⟩
@[simp] def tst : Event := ⟨13, .tc (.st 0 [] .s32x32b)⟩
@[simp] def waitSt : Event := ⟨14, .tc .waitSt⟩
@[simp] def wbar : Event := ⟨15, .warpBar 3 0⟩
@[simp] def exit : Event := ⟨8, .exit⟩

/-- Thread `g` runs `tr g`. -/
def threads (tr : Nat → List Event) : Execution where
  tr := tr
  rf := fun _ _ => none

theorem cluster {n g h : Nat} (hg : g < n) (hh : h < n) : SameCluster (launch n) g h := by
  refine ⟨by simp [launch, Launch.threads]; omega, by simp [launch, Launch.threads]; omega, ?_⟩
  simp [launch, Launch.clusterOfCta, Nat.div_eq_of_lt hg, Nat.div_eq_of_lt hh]

theorem warp {n g h : Nat} (hn : n ≤ 32) (hg : g < n) (hh : h < n) : SameWarp (launch n) g h := by
  refine ⟨⟨by simp [launch, Launch.threads]; omega, by simp [launch, Launch.threads]; omega, ?_⟩,
    ?_⟩
  · simp [launch, Nat.div_eq_of_lt hg, Nat.div_eq_of_lt hh]
  · simp [launch, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hh]
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

theorem po' {X : Execution} {g i j : Nat} (hij : i < j) (hj : j < (X.tr g).length)
    (hna : (X.get (g, i)).bind Event.acc = none := by decide) : po X (g, i) (g, j) :=
  po_of_source_not_access rfl hij hj hna

theorem baseCausalityPo {L : Launch} {X : Execution} {g i j : Nat} (hij : i < j)
    (hj : j < (X.tr g).length) (hna : (X.get (g, i)).bind Event.acc = none := by decide) :
    baseCausality L X (g, i) (g, j) := .single (.inl (po' hij hj hna))

/-- An event of an execution is in its thread's trace. -/
theorem mem_of_get {X : Execution} {e : EvId} {ev : Event} (h : X.get e = some ev) :
    ev ∈ X.tr e.1 := List.mem_of_getElem? h

/-- In an execution without barriers, warp barriers, acquire waits, cluster barriers or
release stores, causality is program order. -/
theorem baseCausality_po {L : Launch} {X : Execution}
    (hk : ∀ g ev, ev ∈ X.tr g → (∀ id c, ev.kind ≠ .bar id c) ∧
      (∀ mask inst, ev.kind ≠ .warpBar mask inst) ∧
      (∀ m q sc, ev.kind ≠ .wait m q true true sc) ∧ (∀ a bs, ev.kind ≠ .wr a bs) ∧
      (∀ sem sc, ev.kind ≠ .fence sem sc) ∧ (∀ a o n, ev.kind ≠ .rmw a o n))
    (hc : ∀ c, X.clusters c = []) {e f : EvId} (h : baseCausality L X e f) : po X e f := by
  refine baseCausality_of_noBar ?_ ?_ ?_ ?_ ?_ ?_ h
  · rintro e k ⟨-, ⟨count, pc, hb⟩, -⟩
    exact (hk _ _ (mem_of_get hb)).1 _ _ rfl
  · rintro w m ⟨pc, q, sc, hw⟩
    exact (hk _ _ (mem_of_get hw)).2.2.1 _ _ _ rfl
  · rintro e f ⟨-, i, j, ⟨phase, ⟨k, s, t, cta, w, lanes, g, hi, -⟩, -⟩, -⟩
    simp [hc] at hi
  · rintro e f ⟨i, j, ⟨-, mask, inst, ⟨pc, hw⟩, -⟩, -⟩
    exact (hk _ _ (mem_of_get hw)).2.1 _ _ rfl
  · rintro e f ⟨a, b, bs, cs, ⟨pc, hw⟩ | ⟨old, pc, hw⟩, -⟩
    · exact (hk _ _ (mem_of_get hw)).2.2.2.1 _ _ rfl
    · exact (hk _ _ (mem_of_get hw)).2.2.2.2.2 _ _ _ rfl
  · rintro e f (⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨sem, sc, hf | hf⟩, -⟩ |
      ⟨⟨sc, -, hs, -⟩, -⟩)
    · obtain ⟨pc, hw⟩ := hf
      exact (hk _ _ (mem_of_get hw)).2.2.2.2.1 _ _ rfl
    · obtain ⟨pc, hw⟩ := hf
      exact (hk _ _ (mem_of_get hw)).2.2.2.2.1 _ _ rfl
    · obtain ⟨pc, hw⟩ := hs
      exact (hk _ _ (mem_of_get hw)).2.2.2.2.1 _ _ rfl

/-! ## 4.1 — pipelined instructions, same thread -/

namespace P41

def X : Execution := threads fun g => if g = 0 then [cp, mmaA, exit] else []

/-- The copy's write precedes the MMA's A read by program order alone. -/
theorem pipelined : TcMma.Pipelined (launch 1) X .cpWrite (0, 0) .aRead (0, 1) :=
  ⟨warp (by decide) (by decide) (by decide), .inl (baseCausalityPo (by decide) (by decide)),
    ⟨0, src, .s128x256b, [0], none⟩, 64, spec (some 0), false, [0, 0, 0, 0], ⟨12, rfl⟩,
    by decide, ⟨1, rfl⟩, rfl⟩

end P41

/-! ## 4.2 — non-pipelined instructions, same thread -/

namespace P42a

def X : Execution := threads fun g => if g = 0 then [tst, waitSt, tld, exit] else []

/-- `tcgen05.wait::st` orders the store before the later load. -/
theorem ordered : TcMma.StoreDoneBefore (launch 1) X (0, 0) (0, 2) :=
  ⟨⟨0, [], .s32x32b, 13, rfl⟩, .inl ⟨(0, 1), ⟨14, rfl⟩, rfl, by decide,
    .inl (baseCausalityPo (by decide) (by decide))⟩⟩

end P42a

namespace P42b

def X : Execution := { threads fun g => if g = 0 then
    [init bar, mma, commit bar, pollR bar, fAfter, tld, exit] else [] with
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (0, 3), .pollParity 0 true)] else [] }

theorem observed : TcMma.CommitObserved (launch 1) X (0, 1) (0, 3) :=
  ⟨false, .cluster, ⟨_, bar, ⟨(0, 2), TcCommit.unicast bar, 0, rfl,
    ⟨rfl, by decide, .inl ⟨0, spec none, false, [0, 0, 0, 0], ⟨1, rfl⟩⟩, _, ⟨5, rfl⟩⟩,
    ⟨5, rfl⟩, TcCommit.target_unicast rfl, by simp [X]⟩, ⟨⟨6, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

/-- MMA, commit, relaxed wait, `fence::after_thread_sync`: the MMA's completion is ordered
before the load. -/
theorem done : TcMma.DoneBefore (launch 1) X (0, 1) (0, 5) :=
  .inr ⟨(0, 3), observed, (0, 4), baseCausalityPo (by decide) (by decide), ⟨11, rfl⟩,
    po' (by decide) (by decide)⟩

/-- The relaxed wait gives no EXT-TCACQUIRE route. -/
theorem no_acquire (w : EvId) (ws : MbarScope) : ¬ AsyncObserved X (0, 1) .mmaDone w true ws := by
  rintro ⟨n, m, -, ⟨pc, q, hw⟩, -⟩
  have hm := mem_of_get hw
  simp only [X, threads] at hm
  split_ifs at hm <;> simp at hm

end P42b

namespace P42bNoFence

def X : Execution := { threads fun g => if g = 0 then
    [init bar, mma, commit bar, pollR bar, tld, exit] else [] with
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (0, 3), .pollParity 0 true)] else [] }

/-- Without `fence::after_thread_sync` the load is not ordered after the MMA's completion. -/
theorem not_done : ¬ TcMma.DoneBefore (launch 1) X (0, 1) (0, 4) := by
  rintro (⟨w, ws, ⟨n, m, -, ⟨pc, q, hw⟩, -⟩, -, -⟩ | ⟨w, -, f, -, ⟨pc, hf⟩, -⟩)
  · have hm := mem_of_get hw
    simp only [X, threads] at hm
    split_ifs at hm <;> simp at hm
  · have hm := mem_of_get hf
    simp only [X, threads] at hm
    split_ifs at hm <;> simp at hm

end P42bNoFence

/-! ## 4.3 — pipelined instructions, different threads of one warp -/

namespace P43

def X : Execution := threads fun g =>
  if g = 0 then [cp, wbar, exit] else if g = 1 then [wbar, mmaA, exit] else []

/-- `bar.warp.sync` orders the copy before the MMA of another lane: a pipelined pair. -/
theorem pipelined : TcMma.Pipelined (launch 2) X .cpWrite (0, 0) .aRead (1, 1) :=
  ⟨warp (by decide) (by decide) (by decide),
    .inl (.single (.inr (.inr (.inr (.inr (.inl ⟨1, 0, ⟨warp (by decide) (by decide)
      (by decide), 3, 0, ⟨15, rfl⟩, ⟨15, rfl⟩⟩, by decide, by decide, by decide⟩)))))),
    ⟨0, src, .s128x256b, [0], none⟩, 64, spec (some 0), false, [0, 0, 0, 0], ⟨12, rfl⟩,
    by decide, ⟨1, rfl⟩, rfl⟩

end P43

namespace P43Fenced

def X : Execution := { threads fun g =>
    if g = 0 then [init bar, cp, fBefore, arriveR bar, exit]
    else if g = 1 then [pollR bar, fAfter, mmaA, exit] else [] with
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.thread (0, 3), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else [] }

theorem exec : MbarExec (launch 2) X (0, 3) (1, 0) :=
  ⟨bar, 0, 1, false, .cluster, false, .cluster, ⟨9, rfl⟩, ⟨⟨6, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

/-- The fences and relaxed mbarrier operations order the copy before the MMA of another
lane: a pipelined pair. -/
theorem pipelined : TcMma.Pipelined (launch 2) X .cpWrite (0, 1) .aRead (1, 2) :=
  ⟨warp (by decide) (by decide) (by decide),
    .inr ⟨(0, 2), po' (by decide) (by decide), ⟨10, rfl⟩,
      ExecOrder.of_obs (f := (1, 1)) (po' (by decide) (by decide)) exec
          (baseCausalityPo (by decide) (by
        decide))
        ⟨11, rfl⟩ (po' (by decide) (by decide))⟩,
    ⟨0, src, .s128x256b, [0], none⟩, 64, spec (some 0), false, [0, 0, 0, 0], ⟨12, rfl⟩,
    by decide, ⟨1, rfl⟩, rfl⟩

end P43Fenced

/-! ## 4.4 — non-pipelined instructions, different threads -/

namespace P44a

def X : Execution := { threads fun g =>
    if g = 0 then [init bar, tld, waitLd, fBefore, arriveR bar, exit]
    else if g = 1 then [pollR bar, fAfter, mma, exit] else [] with
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.thread (0, 4), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else [] }

theorem exec : MbarExec (launch 2) X (0, 4) (1, 0) :=
  ⟨bar, 0, 1, false, .cluster, false, .cluster, ⟨9, rfl⟩, ⟨⟨6, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

/-- Load, `wait::ld`, `fence::before_thread_sync`, relaxed arrive; relaxed wait,
`fence::after_thread_sync`, MMA: the load has completed before the MMA. -/
theorem done : TcMma.WaitBefore (launch 2) X .waitLd (0, 1) (1, 2) :=
  ⟨(0, 2), ⟨3, rfl⟩, rfl, by decide, .inr ⟨(0, 3), po' (by decide) (by decide), ⟨10, rfl⟩,
    ExecOrder.of_obs (f := (1, 1)) (po' (by decide) (by decide)) exec
        (baseCausalityPo (by decide) (by decide))
      ⟨11, rfl⟩ (po' (by decide) (by decide))⟩⟩

end P44a

/-- Causality between the threads of these executions is program order. -/
theorem baseCausality_po_of {X : Execution}
    (hk : ∀ g ev, ev ∈ X.tr g → (∀ id c, ev.kind ≠ .bar id c) ∧
      (∀ mask inst, ev.kind ≠ .warpBar mask inst) ∧
      (∀ m q sc, ev.kind ≠ .wait m q true true sc) ∧ (∀ a bs, ev.kind ≠ .wr a bs) ∧
      (∀ sem sc, ev.kind ≠ .fence sem sc) ∧ (∀ a o n, ev.kind ≠ .rmw a o n))
    (hc : ∀ c, X.clusters c = []) {e f : EvId} (h : baseCausality (launch 2) X e f) : e.1 = f.1 :=
  (baseCausality_po hk hc h).1

namespace P44aNoBefore

def X : Execution := { threads fun g =>
    if g = 0 then [init bar, tld, waitLd, arriveR bar, exit]
    else if g = 1 then [pollR bar, fAfter, mma, exit] else [] with
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.thread (0, 3), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else [] }

/-- Without `fence::before_thread_sync` the load is not ordered before the MMA. -/
theorem not_done : ¬ TcMma.WaitBefore (launch 2) X .waitLd (0, 1) (1, 2) := by
  rintro ⟨w, -, hw1, -, hb | ⟨fb, -, ⟨pc, hf⟩, -⟩⟩
  · have := baseCausality_po_of (fun g ev hm => by
      simp only [X, threads] at hm
      split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl | rfl | rfl | rfl <;>
        simp) (fun _ => rfl) hb
    simp only at hw1 this
    omega
  · have hm := mem_of_get hf
    simp only [X, threads] at hm
    split_ifs at hm <;> simp at hm

end P44aNoBefore

namespace P44aNoAfter

def X : Execution := { threads fun g =>
    if g = 0 then [init bar, tld, waitLd, fBefore, arriveR bar, exit]
    else if g = 1 then [pollR bar, mma, exit] else [] with
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.thread (0, 4), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else [] }

/-- Without `fence::after_thread_sync` the MMA is not ordered after the load. -/
theorem not_done : ¬ TcMma.WaitBefore (launch 2) X .waitLd (0, 1) (1, 1) := by
  rintro ⟨w, -, hw1, -, hb | ⟨fb, -, -, ⟨f, -, ⟨pc, hf⟩, -⟩ | ⟨-, -, -, -, f, -, ⟨pc, hf⟩, -⟩⟩⟩
  · have := baseCausality_po_of (fun g ev hm => by
      simp only [X, threads] at hm
      split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp) (fun _ => rfl) hb
    simp only at hw1 this
    omega
  all_goals
    have hm := mem_of_get hf
    simp only [X, threads] at hm
    split_ifs at hm <;> simp at hm

end P44aNoAfter

namespace P44b

def X : Execution := { threads fun g =>
    if g = 0 then [init bar, mma, commit bar, exit]
    else if g = 1 then [pollR bar, fAfter, tld, exit] else [] with
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else [] }

theorem observed : TcMma.CommitObserved (launch 2) X (0, 1) (1, 0) :=
  ⟨false, .cluster, ⟨_, bar, ⟨(0, 2), TcCommit.unicast bar, 0, rfl,
    ⟨rfl, by decide, .inl ⟨0, spec none, false, [0, 0, 0, 0], ⟨1, rfl⟩⟩, _, ⟨5, rfl⟩⟩,
    ⟨5, rfl⟩, TcCommit.target_unicast rfl, by simp [X]⟩, ⟨⟨6, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

/-- MMA and commit; relaxed wait, `fence::after_thread_sync`, load in another thread: the
MMA's completion is ordered before the load. -/
theorem done : TcMma.DoneBefore (launch 2) X (0, 1) (1, 2) :=
  .inr ⟨(1, 0), observed, (1, 1), baseCausalityPo (by decide) (by decide), ⟨11, rfl⟩,
    po' (by decide) (by decide)⟩

end P44b

namespace P44bNoFence

def X : Execution := { threads fun g =>
    if g = 0 then [init bar, mma, commit bar, exit]
    else if g = 1 then [pollR bar, tld, exit] else [] with
  tcNotified := fun i => if i = (0, 2) then {0} else ∅
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
    (.async (0, 2) (.tcNotify 0), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)] else [] }

/-- Without `fence::after_thread_sync` the load is not ordered after the MMA's completion. -/
theorem not_done : ¬ TcMma.DoneBefore (launch 2) X (0, 1) (1, 1) := by
  rintro (⟨w, ws, ⟨n, m, -, ⟨pc, q, hw⟩, -⟩, -, -⟩ | ⟨w, -, f, -, ⟨pc, hf⟩, -⟩)
  · have hm := mem_of_get hw
    simp only [X, threads] at hm
    split_ifs at hm <;> simp at hm
  · have hm := mem_of_get hf
    simp only [X, threads] at hm
    split_ifs at hm <;> simp at hm

end P44bNoFence

/-! ## The composed example of 4.4 -/

namespace Composed

def X : Execution := { threads fun g =>
    if g = 0 then [init bar, init bar2, mma, commit bar, exit]
    else if g = 1 then [pollR bar, fAfter, fBefore, arriveR bar2, exit]
    else if g = 2 then [pollR bar2, fAfter, tld, exit] else [] with
  tcNotified := fun i => if i = (0, 3) then {0} else ∅
  objects := fun m => if m = bar then replayLog [(.thread (0, 0), .init 1),
      (.async (0, 3) (.tcNotify 0), .arrive 1 0), (.thread (1, 0), .pollParity 0 true)]
    else if m = bar2 then replayLog [(.thread (0, 1), .init 1),
      (.thread (1, 3), .arrive 1 0), (.thread (2, 0), .pollParity 0 true)] else [] }

theorem observed : TcMma.CommitObserved (launch 3) X (0, 2) (1, 0) :=
  ⟨false, .cluster, ⟨_, bar, ⟨(0, 3), TcCommit.unicast bar, 0, rfl,
    ⟨rfl, by decide, .inl ⟨0, spec none, false, [0, 0, 0, 0], ⟨1, rfl⟩⟩, _, ⟨5, rfl⟩⟩,
    ⟨5, rfl⟩, TcCommit.target_unicast rfl, by simp [X]⟩, ⟨⟨6, 0, rfl⟩,
    ⟨1, 2, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        fun _ _ _ h2 _ => absurd h2 (by omega)⟩⟩⟩,
    cluster (by decide) (by decide), cluster (by decide) (by decide)⟩

/-- The relay through the second thread is not an order: the third thread's load is not
ordered after the MMA's completion (EXT-TC-EXEC-ORDER: one observation per ordering). -/
theorem not_done : ¬ TcMma.DoneBefore (launch 3) X (0, 2) (2, 2) := by
  rintro (⟨w, ws, ⟨n, m, -, ⟨pc, q, hw⟩, -⟩, -, -⟩ |
    ⟨w, ⟨acq, ws, ⟨n, m, ⟨c, s, rank, rfl, -, ⟨pcc, hc⟩, htg, -⟩, ⟨⟨pcw, q, hw⟩, -⟩⟩, -⟩,
      f, hb, ⟨pc, hf⟩, hp⟩)
  · have hm := mem_of_get hw
    simp only [X, threads] at hm
    split_ifs at hm <;> simp at hm
  · have hpo := baseCausality_po (fun g ev hm => by
      simp only [X, threads] at hm
      split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl | rfl | rfl | rfl <;>
        simp) (fun _ => rfl) hb
    obtain ⟨wg, wf⟩ := w
    obtain ⟨fg, ff⟩ := f
    obtain ⟨h1, h2, -⟩ := hpo
    obtain ⟨h3, h4, -⟩ := hp
    simp only at h1 h2 h3 h4
    subst h1 h3
    obtain rfl : wf = 0 := by omega
    have hcm := mem_of_get hc
    simp only [X, threads] at hcm
    split_ifs at hcm <;> simp at hcm
    obtain ⟨-, rfl⟩ := hcm
    obtain ⟨-, rfl⟩ := TcCommit.target_unicast_inv rfl htg
    simp [X, threads, Execution.get] at hw

end Composed

end

end PTX.Tests.TcFence
