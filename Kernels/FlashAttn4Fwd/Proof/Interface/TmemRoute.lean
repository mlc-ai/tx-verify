-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Interface.P2
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # What the thread layer exports for the routes through the Tensor Memory objects

The reuse of the P-ready, S-full and O-full objects and the readiness of the accumulator for the
correction's loads go along enabling paths through four objects: the S-full and O-full objects
(the MMA thread's commits, polled by the softmax and the correction), the P-ready object (the
softmax and correction arrivals, polled by the MMA warp) and the statistics named barrier
(the softmax's `bar.arrive`, the correction's `bar.sync`). With `n = kvTiles` tiles per item:

* **softmax** (`soft_p`, `soft_gen`): its P-ready arrival of tile `u` follows its S-full poll of
  tile `u`; its statistics arrival of ordinal `G` follows `genTiles n G` S-full polls (the
  item `G / (n + 1)`'s arrival `G % (n + 1)` follows the polls of its tiles
  `0, 1, …, n - 1, n - 1`), with
  an event between (the last load's wait, the store of `α` or of `l`);
* **correction** (`corr_p`, `corr_ld`): each P-ready arrival of credit `q` is the first
  (`q = 0`), a rescale's, which follows its `bar.sync` of an ordinal `G` with `q + 1 ≤ genTiles n G`
  (`CorrSync`), or a final pass's, which follows its successful O-full poll of item `I` with
  `q ≤ n (I + 1)` (`CorrFinal`); and `q + 1 ≤ n (I' + 1)` with `I'` its successful O-full polls
  before it. A load of the stage's accumulator of credit `q` is a rescale's or a final pass's in
  the same sense;
* **MMA warp** (`mma_commit`, `mma_elect`, `mma_pv`): a commit to an S-full or O-full object is
  issued by a lane of warp 12 of a leader CTA after one of its full-mask elections at which it had
  polled the stage's P-ready objects at least the commit's tile count (S-full: the commits before
  it, on both P-ready objects; O-full: `n` times the items before it, plus `n`); the lanes of the
  warp have polled the P-ready objects equally often at their elections of one ordinal (the
  election ordinals of one instance agree by `ElectOrdinal`); a PV MMA of tile `u` of item `I`
  has `n I < u + 1` polls.

The fields are event-level facts of single threads from the run invariants of the softmax
(`Softmax.Counts`), the correction (`Correction.Counts`) and the MMA warp (`Mma.Counts`);
`mma_elect` compares lanes of one warp running the same counts. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

theorem kvTiles_pos {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    0 < kvTiles L := by
  have h1 := skOf_eq hpre
  have h2 := hpre.skPos
  unfold kvTiles
  omega

/-- The S-full polls before a softmax thread's statistics arrival of ordinal `G`, with `n` tiles
per item. -/
def genTiles (n G : Nat) : Nat := n * (G / (n + 1)) + min (G % (n + 1) + 1) n

/-- Commits of thread `g` to stage `st`'s O-full object of its CTA before its event `i`. -/
def oFullCommits (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  ((X.tr g).take i).countP (commitsTo (oFullBar L (ctaOf L g) st))

/-- A correction thread's event `i` of stage `st` follows its `bar.sync` on its statistics
barrier of the stage of an ordinal `G` with `v ≤ genTiles n G`. -/
def CorrSync (L : Launch) (X : Execution) (h st i v : Nat) : Prop :=
  ∃ y pc, y < i ∧
    X.get (h, y) = some ⟨pc, .bar (statsId st (warpOf L h - 8)) (some 64) .sync⟩ ∧
    v ≤ genTiles (kvTiles L) (barOrd X h y (statsId st (warpOf L h - 8)))

/-- A correction thread's event `i` of stage `st` follows its successful O-full poll of the stage
with `I` earlier ones and `v ≤ n (I + 1)`. -/
def CorrFinal (L : Launch) (X : Execution) (h st i v : Nat) : Prop :=
  ∃ j pc p acq sc, j < i ∧
    X.get (h, j) = some ⟨pc, .wait (oFullBar L (ctaOf L h) st) p true acq sc⟩ ∧
    v ≤ kvTiles L * (okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take j) + 1)

/-- The thread layer's facts for the routes through the Tensor Memory objects. -/
structure RouteFacts (L : Launch) (X : Execution) : Prop where
  /-- A softmax arrival on its stage's P-ready object follows its S-full poll of the tile. -/
  soft_p : ∀ {g i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    warpOf L g < 8 →
    X.get (g, i) = some ⟨pc,
      .arrive (pReadyBar L (leadCta (ctaOf L g)) (warpOf L g / 4)) tx cnt rel sc⟩ →
    pArr L X g (warpOf L g / 4) i + 1 ≤ sPolls L X g (warpOf L g / 4) i
  /-- A softmax statistics arrival of ordinal `G` follows `genTiles n G` S-full polls, with an
  event between. -/
  soft_gen : ∀ {g a pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    warpOf L g < 8 → X.get (g, a) = some ⟨pc, .bar id cnt m⟩ → id ≠ 2 →
    ∃ e < a, genTiles (kvTiles L) (barOrd X g a id) ≤ sPolls L X g (warpOf L g / 4) e
  /-- A correction arrival of credit `q` on stage `st`'s P-ready object: `q + 1 ≤ n (I' + 1)` with
  `I'` its successful O-full polls of the stage before it, and it is the first, a rescale's or a
  final pass's. -/
  corr_p : ∀ {h i pc tx cnt st : Nat} {rel : Bool} {sc : MbarScope}, h < L.threads →
    8 ≤ warpOf L h → warpOf L h < 12 → st < 2 →
    X.get (h, i) = some ⟨pc, .arrive (pReadyBar L (leadCta (ctaOf L h)) st) tx cnt rel sc⟩ →
    pArr L X h st i + 1 ≤
        kvTiles L * (okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take i) + 1) ∧
      (pArr L X h st i = 0 ∨ CorrSync L X h st i (pArr L X h st i + 1) ∨
        CorrFinal L X h st i (pArr L X h st i))
  /-- A correction load reads some values of one stage's accumulator; of credit `q`, it is a
  rescale's or a final pass's. -/
  corr_ld : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → X.TLd (h, i) a vals .s32x32b → ∃ st < 2, 0 < vals.length ∧
      (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧
      (CorrSync L X h st i (pArr L X h st i + 1) ∨ CorrFinal L X h st i (pArr L X h st i))
  /-- A commit to stage `st`'s S-full or O-full object is a lane's of warp 12 of a leader CTA,
  after one of its full-mask elections at which it had polled the stage's P-ready objects at least
  the commit's tile count. -/
  mma_commit : ∀ {y : EvId} {s : TcCommit.Spec} {st : Nat}, X.Commit y s → st < 2 →
    (s.mbar = sFullBar L (ctaOf L y.1) st ∨ s.mbar = oFullBar L (ctaOf L y.1) st) →
    y.1 < L.threads ∧ warpOf L y.1 = 12 ∧ leadCta (ctaOf L y.1) = ctaOf L y.1 ∧
      ∃ k pc inst l, k < y.2 ∧ X.Elect (y.1, k) pc fullMask inst l ∧
        (s.mbar = sFullBar L (ctaOf L y.1) st → sCommits L X y.1 st y.2 ≤ pPolls L X y.1 st k ∧
          sCommits L X y.1 st y.2 ≤ p2Polls L X y.1 st k) ∧
        (s.mbar = oFullBar L (ctaOf L y.1) st →
          kvTiles L * (oFullCommits L X y.1 st y.2 + 1) ≤ pPolls L X y.1 st k)
  /-- The lanes of the MMA warp have polled the P-ready objects equally often at their elections
  of one ordinal. -/
  mma_elect : ∀ {h h' e e' pc pc' mask mask' inst inst' l l' st : Nat}, h < L.threads →
    warpOf L h = 12 → SameWarp L h h' → st < 2 → X.Elect (h, e) pc mask inst l →
    X.Elect (h', e') pc' mask' inst' l' →
    ((X.tr h).take e).countP isElectEv = ((X.tr h').take e').countP isElectEv →
    pPolls L X h st e = pPolls L X h' st e' ∧ p2Polls L X h st e = p2Polls L X h' st e'
  /-- A PV MMA of tile `u` of item `I` (`I` O-full commits of its stage before it) has `n I < u + 1`
  P-ready polls of its stage before it. -/
  mma_pv : ∀ {x : EvId} {cell : Cell} {st : Nat}, IsMma X x → X.MmaCell x cell → InO st cell →
    kvTiles L * oFullCommits L X x.1 st x.2 < pPolls L X x.1 st x.2

end
end PTX.Kernels.FlashAttn4Fwd.Proof
