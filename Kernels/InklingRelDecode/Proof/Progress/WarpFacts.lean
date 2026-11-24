-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Collective

@[expose] public section

/-!
# What the thread layer exports for the progress at the warp collectives

A warp collective (`shfl.sync`, `elect.sync`, `bar.warp.sync`) is performed by the lanes of a warp
together: Core admits a lane's event only with the events of the other lanes of its instance
(DEP-WARP-SHUFFLE, DEP-WARP-ELECT, DEP-WARP-BARRIER). A released thread at a warp collective steps
when every lane of its warp is at the same collective and released (the warp performs it), or when
a lane of the warp is not yet there and is earlier (it ranks below). The lanes of a warp run one
role on one schedule, so their collectives agree by ordinal (`Sched.isWarpColl` counts them). The
fields of `WarpCollFacts`, each a fact of single threads' events and machine states, with functions
of the warp (`warpKey`) and the ordinal:

* `shape`: the `n`-th warp collective of a lane has a static part (`Sched.CollShape`: the shuffle
  mode and lane operands, or the member mask) and, for the next one, a source position fixed by the
  warp and `n`; every mask names the whole warp (`Sched.CollShape.Full`). A thread at a
  warp-collective state fires a template of that shape at that position, or undefined behaviour.
* `last`: the warp and `n` fix at most one blocking synchronizing event (`SyncEv`): a register
  request (position, operands, ordinal), a warp-collective `tcgen05` event other than a
  `cta_group::2` allocator operation (ordinal), or a `bar.sync` (barrier id and ordinal on that id).
  A lane at its `n`-th warp collective has made that event, and its last event is that event or
  never blocks (`LastFree`); with no event fixed, its last event never blocks.
* `exit`: a lane exits after a number of warp collectives fixed by its warp, more than any lane at
  a warp collective has made.
* `lag`: in a maximal execution, a lane of the warp of a released thread at its `n`-th warp
  collective that has made at most `n` of them and is not at its `n`-th is earlier (and the
  thread's time is positive). In a prefix that is not maximal a lane may have stopped one time
  unit before the collective; the consumer (`warp_next_steps`) has a maximal execution and a
  released thread.

`WarpCollFacts` is asked of maximal executions (`Remaining.warpColl`); `shape`, `last` and `exit`
hold of every consistent execution.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

/-- A blocking synchronizing event of a lane, by what the lanes of its warp share: a register
request (position, direction, count, ordinal), a warp-collective `tcgen05` event (whether it is
an allocator operation, ordinal), or a `bar.sync` (barrier id, ordinal among the thread's events
on that id). -/
inductive SyncEv where
  | reg (pc : Nat) (inc : Bool) (n o : Nat)
  | tc (res : Bool) (k : Nat)
  | bar (id o : Nat)

/-- Event `j` of thread `g` is the synchronizing event `x`. A `tcgen05` event is not a
`cta_group::2` allocator operation. -/
def SyncAt (X : Execution) (g j : Nat) : SyncEv → Prop
  | .reg pc inc n o => ∃ inst, X.get (g, j) = some ⟨pc, .setMaxReg inc n inst⟩ ∧
      SetMaxNReg.ordinal X (g, j) = o
  | .tc res k => X.TcK (g, j) k ∧
      (∀ pc dst act, X.get (g, j) ≠ some ⟨pc, .tc (.resource .two dst act)⟩) ∧
      ((∃ pc grp dst act, X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩) ↔ res = true)
  | .bar id o => ∃ cnt pc, X.IsBarrier (g, j) id cnt pc ∧
      ((X.tr g).take j).countP (Execution.isBarId id) = o

/-- The last event of thread `g`, if any, never blocks. -/
def LastFree (X : Execution) (g : Nat) : Prop :=
  ∀ q, X.get (g, (X.tr g).length - 1) = some q → Sched.Unblocking q.kind

/-- The warp of a thread in the grid: its CTA and its warp in the CTA. -/
def warpKey (L : Launch) (g : Nat) : Nat × Nat := (g / L.block, g % L.block / 32)

/-- Two threads of a warp have one key. -/
theorem warpKey_eq {L : Launch} {g h : Nat} (hw : SameWarp L g h) :
    warpKey L g = warpKey L h := by
  obtain ⟨⟨-, -, hc⟩, hwp⟩ := hw
  simp only [warpKey, hc, hwp]

/-- **The thread layer's facts for the progress at the warp collectives.** -/
structure WarpCollFacts (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (X : Execution) :
    Prop where
  /-- The static part of a lane's `n`-th warp collective, and the source position of its next one,
  are a function of the warp and `n`; every mask names the whole warp. -/
  shape : ∃ F : Nat × Nat → Nat → Nat × Sched.CollShape,
    (∀ key n, (F key n).2.Full) ∧
    (∀ {g k : Nat} {e : Event} {d : TSt}, g < L.threads → St Q L X g k = some (some d) →
      X.get (g, k) = some e → Sched.isWarpColl e = true →
      Sched.kindShape e.kind =
        some (F (warpKey L g) (((X.tr g).take k).countP Sched.isWarpColl)).2) ∧
    (∀ {g : Nat} {d : TSt} {t : TState} {m : Tmpl}, g < L.threads →
      St Q L X g (X.tr g).length = some (some d) → nextKind d = .warp →
      (threadCode L g Q).AtD d t → out kernel asms L g t = .ev m → (∃ f, m = .ub f) ∨
        (t.pc = (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).1 ∧
          Sched.tmplShape m = some (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).2))
  /-- The warp and `n` fix at most one blocking synchronizing event. A lane at its `n`-th warp
  collective has made it, and its last event is it or never blocks; with none fixed, the last
  event never blocks. -/
  last : ∃ R : Nat × Nat → Nat → Option SyncEv,
    ∀ {g : Nat} {d : TSt}, g < L.threads → St Q L X g (X.tr g).length = some (some d) →
      nextKind d = .warp →
      match R (warpKey L g) ((X.tr g).countP Sched.isWarpColl) with
      | none => LastFree X g
      | some x => (∃ j, j < (X.tr g).length ∧ SyncAt X g j x) ∧
        (LastFree X g ∨ SyncAt X g ((X.tr g).length - 1) x)
  /-- A lane exits after a number of warp collectives fixed by its warp, more than a lane at a warp
  collective has made. -/
  exit : ∃ N : Nat × Nat → Nat,
    (∀ {g : Nat} {d : TSt}, g < L.threads → St Q L X g (X.tr g).length = some (some d) →
      nextKind d = .warp → (X.tr g).countP Sched.isWarpColl < N (warpKey L g)) ∧
    (∀ {g k pc : Nat} {d : TSt}, g < L.threads → St Q L X g k = some (some d) →
      X.get (g, k) = some ⟨pc, .exit⟩ → N (warpKey L g) ≤ ((X.tr g).take k).countP Sched.isWarpColl)
  /-- A lane of the warp of a released thread at its `n`-th warp collective that has made at most
  `n` of them and is not at its `n`-th is earlier (`Sched.threadTime`), and the thread's time is
  positive. -/
  lag : ∀ {g h : Nat} {d : TSt}, g < L.threads → h < L.threads → SameWarp L g h →
    St Q L X g (X.tr g).length = some (some d) → nextKind d = .warp → Step.Released L X g →
    (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl →
    ¬ ((X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧
      ∃ d', St Q L X h (X.tr h).length = some (some d') ∧ nextKind d' = .warp) →
    0 < T g d ∧ Sched.threadTime (timed T Q L) X h < T g d

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
