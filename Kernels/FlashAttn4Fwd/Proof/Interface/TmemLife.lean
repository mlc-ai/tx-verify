-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute

@[expose] public section

/-! # What the thread layer exports for the lifetime of the Tensor Memory allocation

Barrier 2 (`bar.sync 2, 416` / `bar.arrive 2, 416`) has two generations, made by the 13 warps
0-12 of each CTA (the softmax warps 0-7, the correction warps 8-11 and the MMA warp 12):

* **generation 0** (ordinal 0): warp 12's `bar.sync` right after its allocation (PTX 715), the
  softmax's (1619) and the correction's (4521) before their first Tensor Memory access; the MMA
  warp issues its MMAs after it;
* **generation 1** (ordinal 1): warp 12's `bar.sync` after relinquishing the allocation permit
  (1505), the softmax's (4513) and the correction's (5704) `bar.arrive` after their last
  `tcgen05` event (load, store, `wait::ld` or `wait::st`) and, for the correction, after its
  O-full polls of every item.

After its `bar.sync` of ordinal 1 a thread of warp 12 arrives (release, at cluster scope by the
assumption `clusterMbar`) on the other CTA's handshake barrier `+320`, then polls its own until
an acquire poll (cluster scope) succeeds, and deallocates.

The fields are facts of single threads' events, to be proved from the run invariants of the
softmax, correction and MMA roles. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- Thread `g`'s event `b` is a `bar.sync 2, 416` with `o` earlier events on barrier 2. -/
def Bar2Sync (X : Execution) (g b o : Nat) : Prop :=
  ∃ pc, X.get (g, b) = some ⟨pc, .bar 2 (some 416) .sync⟩ ∧ barOrd X g b 2 = o

/-- The thread layer's facts for the lifetime of the Tensor Memory allocation. -/
structure TmemLifeFacts (L : Launch) (X : Execution) : Prop where
  /-- An event on barrier 2 is a thread's of warps 0-12. -/
  bar2_warp : ∀ {g i pc : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩ → warpOf L g < 13
  /-- An event of a thread of warp 12 on barrier 2 follows the thread's allocation. -/
  bar2_alloc : ∀ {g b pc : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    warpOf L g = 12 → X.get (g, b) = some ⟨pc, .bar 2 cnt m⟩ →
      ∃ j < b, ∃ pca grp dst n, X.get (g, j) = some ⟨pca, .tc (.resource grp dst (.alloc n))⟩
  /-- A thread of warps 0-12 exits after two events on barrier 2. -/
  exit_bar2 : ∀ {g k pc : Nat}, g < L.threads → warpOf L g < 13 →
    X.get (g, k) = some ⟨pc, .exit⟩ → 2 ≤ barOrd X g k 2
  /-- A softmax or correction Tensor Memory load or store follows the thread's `bar.sync 2` of
  ordinal 0. -/
  tc_sync : ∀ {h k a : Nat} {vals : List Value}, h < L.threads → warpOf L h < 12 →
    (X.TLd (h, k) a vals .s32x32b ∨ X.TSt (h, k) a vals .s32x32b) → ∃ b < k, Bar2Sync X h b 0
  /-- An MMA follows its thread's `bar.sync 2` of ordinal 0. -/
  mma_sync : ∀ {x : EvId}, IsMma X x → ∃ b < x.2, Bar2Sync X x.1 b 0
  /-- A softmax or correction `tcgen05` event (a load, a store or a wait for one) has at most one
  event on barrier 2 before it. -/
  wait_bar2 : ∀ {h k pc : Nat} {wk : TcKind}, h < L.threads → warpOf L h < 12 →
    X.get (h, k) = some ⟨pc, .tc wk⟩ → barOrd X h k 2 ≤ 1
  /-- A correction thread's event on barrier 2 of ordinal 1 follows, for each stage, one
  successful poll of the stage's O-full object of its CTA per item of its cluster. -/
  corr_items : ∀ {h b pc st I : Nat} {cnt : Option Nat} {m : BarMode}, h < L.threads →
    8 ≤ warpOf L h → warpOf L h < 12 → X.get (h, b) = some ⟨pc, .bar 2 cnt m⟩ →
    barOrd X h b 2 = 1 → st < 2 → workOf L h I < totOf L →
      I + 1 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take b)
  /-- An MMA is in an item of its cluster: for a stage, the work item of its O-full commits
  before it is below the item count. -/
  mma_item : ∀ {x : EvId}, IsMma X x →
    ∃ st < 2, workOf L x.1 (oFullCommits L X x.1 st x.2) < totOf L
  /-- A deallocation follows its thread's `bar.sync 2` of ordinal 1. -/
  dealloc_sync : ∀ {g k pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ → ∃ b < k, Bar2Sync X g b 1
  /-- A deallocation follows its thread's successful acquire poll, at cluster scope, of its CTA's
  handshake barrier. -/
  dealloc_wait : ∀ {g k pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
      ∃ w < k, ∃ pcw p, X.get (g, w) =
        some ⟨pcw, .wait (FBar.loc L (ctaOf L g) .dealloc) p true true .cluster⟩
  /-- An arrival on a handshake barrier is a release at cluster scope, after its thread's
  `bar.sync 2` of ordinal 1. -/
  hs_release : ∀ {g y pc tx c cta : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    X.get (g, y) = some ⟨pc, .arrive (FBar.loc L cta .dealloc) tx c rel sc⟩ →
      rel = true ∧ sc = .cluster ∧ ∃ b < y, Bar2Sync X g b 1

end
end PTX.Kernels.FlashAttn4Fwd.Proof
