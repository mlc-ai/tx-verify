-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressNext
public import Kernels.FlashAttn4Fwd.Proof.Interface.WarpSync
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-! # What the thread layer exports for the progress at the warp collectives

A warp collective (`shfl.sync`, `elect.sync`, `bar.warp.sync`, `vote.sync`) is performed by the
lanes of a warp together: Core admits a lane's event only with the events of the other lanes of
its instance (DEP-WARP-SHUFFLE, DEP-WARP-ELECT, DEP-WARP-BARRIER, DEP-WARP-VOTE). A released thread
at a warp collective steps when every lane of its warp is at the same collective and released (the
warp performs it), or when a lane of the warp is not yet there and is earlier (it ranks below). The
lanes of a warp run one role on one work schedule, so their collectives agree by ordinal
(`Sched.isWarpColl` counts them). The fields, each a fact of single threads' events and machine
states, with functions of the warp (`warpKey`) and the ordinal:

* `shape`: the `n`-th warp collective of a lane has a static part (`Sched.CollShape`: the shuffle
  mode and lane operands, or the member mask) and, for the next one, a source position fixed by the
  warp and `n`; every mask names the whole warp (`Sched.CollShape.Full`). A thread at a
  warp-collective state fires a template of that shape at that position, or undefined behaviour.
* `last`: the last event of a thread before its `n`-th warp collective never blocks
  (`Sched.Unblocking`), or it is the thread's first register request, whose operands are fixed by
  the warp and `n` (the loader's rank broadcast follows its `setmaxnreg`), or it is a
  warp-collective `tcgen05` event other than a paired Tensor Memory operation, whose ordinal is
  fixed by the warp and `n` (the softmax warp barrier follows a `tcgen05.wait::st`).
* `exit`: a lane exits after a number of warp collectives fixed by its warp, more than any lane
  at a warp collective has made.
* `lag`: a lane of the warp of a thread at its `n`-th warp collective that has made at most `n`
  of them and is not at its `n`-th is at an earlier state (and the thread is not at the first
  state of the machine, time 0). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The thread layer's facts for the progress at the warp collectives. -/
structure WarpCollFacts (L : Launch) (X : Execution) : Prop where
  /-- The static part of a lane's `n`-th warp collective, and the source position of its next
  one, are a function of the warp and `n`; every mask names the whole warp. -/
  shape : ∃ F : Nat × Nat → Nat → Nat × Sched.CollShape,
    (∀ key n, (F key n).2.Full) ∧
    (∀ {g k : Nat} {e : Event} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
      X.get (g, k) = some e → Sched.isWarpColl e = true →
      Sched.kindShape e.kind =
        some (F (warpKey L g) (((X.tr g).take k).countP Sched.isWarpColl)).2) ∧
    (∀ {g : Nat} {d : ThreadD} {t : TState} {m : Tmpl}, g < L.threads →
      St L X g (X.tr g).length = some (some d) → nextKind d = .warp → (code L g).AtD d t →
      out kernel asms L g t = .ev m → (∃ f, m = .ub f) ∨
        (t.pc = (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).1 ∧
          Sched.tmplShape m = some (F (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).2))
  /-- The last event before a lane's `n`-th warp collective never blocks, or it is the lane's
  first register request, with operands fixed by the warp and `n`, or it is a warp-collective
  `tcgen05` event other than a paired Tensor Memory operation, of an ordinal fixed by the warp
  and `n`. -/
  last : ∃ R : Nat × Nat → Nat → Option ((Nat × Bool × Nat) ⊕ Nat),
    ∀ {g : Nat} {d : ThreadD}, g < L.threads → St L X g (X.tr g).length = some (some d) →
      nextKind d = .warp →
      match R (warpKey L g) ((X.tr g).countP Sched.isWarpColl) with
      | none => ∀ q, X.get (g, (X.tr g).length - 1) = some q → Sched.Unblocking q.kind
      | some (.inl (pc, inc, n)) => ∃ inst,
        X.get (g, (X.tr g).length - 1) = some ⟨pc, .setMaxReg inc n inst⟩ ∧
          SetMaxNReg.ordinal X (g, (X.tr g).length - 1) = 0
      | some (.inr k) => X.TcK (g, (X.tr g).length - 1) k ∧
        ∀ pc grp dst act, X.get (g, (X.tr g).length - 1) ≠ some ⟨pc, .tc (.resource grp dst act)⟩
  /-- A lane exits after a number of warp collectives fixed by its warp, more than a lane at a
  warp collective has made. -/
  exit : ∃ T : Nat × Nat → Nat,
    (∀ {g : Nat} {d : ThreadD}, g < L.threads → St L X g (X.tr g).length = some (some d) →
      nextKind d = .warp → (X.tr g).countP Sched.isWarpColl < T (warpKey L g)) ∧
    (∀ {g k pc : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
      X.get (g, k) = some ⟨pc, .exit⟩ → T (warpKey L g) ≤ ((X.tr g).take k).countP Sched.isWarpColl)
  /-- A lane of the warp of a thread at its `n`-th warp collective that has made at most `n` of
  them and is not at its `n`-th is earlier (`endTime`), and the thread's time is positive. -/
  lag : ∀ {g h : Nat} {d : ThreadD}, g < L.threads → h < L.threads → SameWarp L g h →
    St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
    (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl →
    ¬ ((X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧
      ∃ d', St L X h (X.tr h).length = some (some d') ∧ nextKind d' = .warp) →
    0 < stateTime L g d ∧ endTime L X h < stateTime L g d

end
end PTX.Kernels.FlashAttn4Fwd.Proof
