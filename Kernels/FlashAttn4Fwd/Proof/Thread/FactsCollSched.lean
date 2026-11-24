-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWarp
public import Lemmas.Kernel.Progress.Sched

@[expose] public section

/-! # Collective schedules and the waits at the collectives

A collective (the events `p` selects: warp-collective `tcgen05` events, paired Tensor Memory
operations, the events on one named barrier, the warp collectives) is scheduled for a group of
threads by a function `S` of the group's key and the ordinal (`CollSched`): a state whose event
is the thread's `n`-th collective has time `S key n`, a state whose event is not a collective is
earlier than the thread's next collective, a state at the trace's end is no later than it, and
`S` increases with the ordinal. The functions are the roles' site-time tables at the collective
sites (`Thread/Roles.lean`): a thread's time follows its program order, and the lanes (or, for the
paired operations, the warps 12 of a pair) reach their `n`-th collective at one site, item and
trip. A named barrier's schedule is per participant warp (`BarSchedW`): the participants'
`n`-th events are at different times (arrivals before waits), and a waiting `bar.sync` is no
earlier than the other participants' events of its ordinal.

From a schedule, a thread that has made at most `n` collectives is no later (`endTime`) than the
time of the `n`-th (`Sched.threadTime_le_sched`), its machine stopped or not. This gives the lag
fields of `TcWaitFacts`, `TmemWaitFacts` and `BarWaitFacts`, and, with the warp collectives'
schedule and its strictness clauses (`WarpSched`), the lag of `WarpCollFacts`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow Tmem.Pair

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The fields -/

/-- The warp-collective `tcgen05` schedule of each warp (per role: the MMA warp's allocation,
relinquishment and deallocation, the softmax and correction warps' loads, stores and waits). -/
def TcSched (L : Launch) (X : Execution) : Prop :=
  ∃ S, Sched.CollSched (timed L) X isTcColl (warpKey L) (fun _ => True) S

/-- **A lane of the warp that has made at most `k` warp-collective `tcgen05` events is no later
than the thread's state before its `k`-th.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TcWaitFacts_lag (hs : TcSched L X) :
    ∀ {g h j k : Nat} {d : ThreadD}, g < L.threads → h < L.threads → SameWarp L g h →
      X.TcK (g, j) k → St L X g j = some (some d) → (X.tr h).countP isTcColl ≤ k →
      endTime L X h ≤ stateTime L g d := by
  intro g h j k d hg hh hw hK hσ hc
  obtain ⟨S, hS⟩ := hs
  obtain ⟨⟨e, he, hp⟩, hk⟩ := hK
  exact Sched.lag_of_sched hS hg hh trivial trivial (warpKey_eq hw).symm hσ he hp (hk ▸ hc)

/-- The paired Tensor Memory operations' schedule of the warps 12 of a pair (MMA package). -/
def TmemSched (L : Launch) (X : Execution) : Prop :=
  ∃ S, Sched.CollSched (timed L) X isTmemOp (fun g => ctaOf L g / 2) (fun g => warpOf L g = 12) S

/-- **A lane of warp 12 of the pair that has made at most `n` operations is no later than the
state of `g` before its `n`-th.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TmemWaitFacts_lag (hs : TmemSched L X)
    (hwarp : ∀ {g j pc grp dst act}, g < L.threads →
      X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩ → warpOf L g = 12) :
    ∀ {g h j n : Nat} {d : ThreadD}, g < L.threads → h < L.threads →
      warpOf L h = 12 → ctaOf L h / 2 = ctaOf L g / 2 →
      (∃ pc grp dst act, X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩) →
      tmemOps ((X.tr g).take j) = n → St L X g j = some (some d) →
      tmemOps (X.tr h) ≤ n → endTime L X h ≤ stateTime L g d := by
  intro g h j n d hg hh hwh hcta ⟨pc, grp, dst, act, he⟩ hn hσ hc
  obtain ⟨S, hS⟩ := hs
  exact Sched.lag_of_sched hS hg hh (hwarp hg he) hwh hcta hσ he rfl
    (by unfold tmemOps at hn hc; omega)

/-- **The schedule of named barrier `id`**, per participant warp: exact at each warp's own
events (the warp is the key), and at a thread's `n`-th event, when it is a `bar.sync`, every
participant warp of the CTA has its `n`-th event no later (the arrivals are scheduled before the
waits: the softmax and correction warps' end arrival before the MMA warp's second `bar.sync`, a
softmax warp's statistics arrival before the correction warp's sync of the same ordinal). -/
structure BarSchedW (L : Launch) (X : Execution) (id : Nat) (S : Nat × Nat → Nat → Nat) :
    Prop where
  /-- Each participant warp's events on the barrier are at its schedule's times. -/
  sched : Sched.CollSched (timed L) X (Execution.isBarId id) (warpKey L)
    (fun g => BarGroup id (warpOf L g)) S
  /-- At a thread's `bar.sync`, every participant warp of the CTA has its event of the same
  ordinal no later. -/
  sync : ∀ {g y j pc : Nat} {cnt : Option Nat} {d : ThreadD}, g < L.threads → y < L.threads →
    y / L.block = g / L.block → BarGroup id (warpOf L y) →
    X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩ → St L X g j = some (some d) →
    S (warpKey L y) (barOrd X g j id) ≤ S (warpKey L g) (barOrd X g j id)

/-- The schedules of every named barrier (per role: the softmax, correction and MMA warps'
barrier sites). -/
def BarSched (L : Launch) (X : Execution) : Prop := ∀ id, ∃ S, BarSchedW L X id S

/-- A thread's event on named barrier `id` is a participant warp's (per role: the barrier ids
of each role's sites; barrier 2's part is `bar_warp13`). -/
def BarMember (L : Launch) (X : Execution) : Prop :=
  ∀ {g j pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    X.get (g, j) = some ⟨pc, .bar id cnt m⟩ → BarGroup id (warpOf L g)

/-- A participant lane of the CTA that has made no more events on a barrier than a thread before
its event there has not exited (per role: a lane exits after all its barrier events). -/
def BarNoExit (L : Launch) (X : Execution) : Prop :=
  ∀ {g y j pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads → y < L.threads →
    y / L.block = g / L.block → BarGroup id (warpOf L y) →
    X.get (g, j) = some ⟨pc, .bar id cnt m⟩ →
    (X.tr y).countP (Execution.isBarId id) ≤ barOrd X g j id →
    ∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩

theorem isBarId_bar {pc id : Nat} {cnt : Option Nat} {m : BarMode} :
    Execution.isBarId id ⟨pc, .bar id cnt m⟩ = true := by
  simp [Execution.isBarId]

/-- **`BarWaitFacts.lag_sync`.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.BarWaitFacts_lag_sync (hs : BarSched L X)
    (hmem : BarMember L X) (hne : BarNoExit L X) :
    ∀ {g y j pc id : Nat} {cnt : Option Nat} {d : ThreadD},
      g < L.threads → y < L.threads → y / L.block = g / L.block → BarGroup id (warpOf L y) →
      X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩ → St L X g j = some (some d) →
      (X.tr y).countP (Execution.isBarId id) ≤ barOrd X g j id →
        (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ endTime L X y ≤ stateTime L g d := by
  intro g y j pc id cnt d hg hy hc hG he hσ hcnt
  obtain ⟨S, hS⟩ := hs id
  refine ⟨hne hg hy hc hG he hcnt, ?_⟩
  rw [show stateTime L g d = _ from hS.sched.atEv hg (hmem hg he) hσ he isBarId_bar]
  exact (Sched.threadTime_le_sched hS.sched hy hG).trans
    ((Sched.sched_le hS.sched.mono _ hcnt).trans (hS.sync hg hy hc hG he hσ))

/-- **`BarWaitFacts.lag_warp`.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.BarWaitFacts_lag_warp (hs : BarSched L X)
    (hmem : BarMember L X) (hne : BarNoExit L X) :
    ∀ {g y j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : ThreadD},
      g < L.threads → y < L.threads → SameWarp L g y →
      X.get (g, j) = some ⟨pc, .bar id cnt m⟩ → St L X g j = some (some d) →
      (X.tr y).countP (Execution.isBarId id) ≤ barOrd X g j id →
        (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ endTime L X y ≤ stateTime L g d := by
  intro g y j pc id cnt m d hg hy hw he hσ hcnt
  obtain ⟨S, hS⟩ := hs id
  have hG := hmem hg he
  have hwe : warpOf L y = warpOf L g := hw.2.symm
  have hc : y / L.block = g / L.block := hw.1.2.2.symm
  have hGy : BarGroup id (warpOf L y) := hwe ▸ hG
  exact ⟨hne hg hy hc hGy he hcnt,
    Sched.lag_of_sched hS.sched hg hy hG hGy (warpKey_eq hw).symm hσ he isBarId_bar hcnt⟩

/-- After a warp-collective `tcgen05` event the machine continues at a later state or has stopped
(per role: the site after each such site is timed later; the correction stops at a load's wait
whose chunk its products reject). -/
def TcStepUp (L : Launch) (X : Execution) : Prop :=
  ∀ {g j k : Nat} {d : ThreadD}, g < L.threads → X.TcK (g, j) k →
    St L X g j = some (some d) →
      (∃ d', St L X g (j + 1) = some (some d') ∧ stateTime L g d < stateTime L g d') ∨
        St L X g (j + 1) = none

/-- After a named-barrier event the machine continues at a later state or has stopped (per role;
the softmax after `gen` may stop). -/
def BarStepUp (L : Launch) (X : Execution) : Prop :=
  ∀ {g j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : ThreadD}, g < L.threads →
    X.get (g, j) = some ⟨pc, .bar id cnt m⟩ → St L X g j = some (some d) →
      (∃ d', St L X g (j + 1) = some (some d') ∧ stateTime L g d < stateTime L g d') ∨
        St L X g (j + 1) = none

/-- **`TcWaitFacts`** from the schedule and the step's time. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.tcWaitFacts (hs : TcSched L X)
    (hu : TcStepUp L X) : TcWaitFacts L X where
  lag := TcWaitFacts_lag hs
  after := hu

/-- **`TmemWaitFacts`** from the schedule. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.tmemWaitFacts (hs : TmemSched L X)
    (hwarp : ∀ {g j pc grp dst act}, g < L.threads →
      X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩ → warpOf L g = 12) :
    TmemWaitFacts L X where
  lag := TmemWaitFacts_lag hs hwarp

/-- **`BarWaitFacts`** from the schedules, the participants and the steps' times. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.barWaitFacts (hs : BarSched L X)
    (hmem : BarMember L X) (hne : BarNoExit L X) (hu : BarStepUp L X) : BarWaitFacts L X where
  after := hu
  lag_warp := BarWaitFacts_lag_warp hs hmem hne
  lag_sync := BarWaitFacts_lag_sync hs hmem hne

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
