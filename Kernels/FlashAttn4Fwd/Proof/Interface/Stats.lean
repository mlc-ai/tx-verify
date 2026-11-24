-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bars
public import Kernels.FlashAttn4Fwd.Proof.Thread.Common
public import Lemmas.Protocol.NamedBarWarp
public import Lemmas.Flow.Polls

@[expose] public section

/-! # What the thread layer exports for the statistics handoff

Softmax warp `w < 8` handles stage `st = w / 4`, rows `32 (w % 4) + lane` of that stage;
correction warp `w ∈ [8, 12)` handles rows `32 (w - 8) + lane` of both stages. Every row's
softmax thread hands its per-row scale (the rescale factor `α`, then the final row sum `l`) to the
row's correction thread through one 4-byte word of shared memory (`statsWord`, offset
`332 + 512 st + 4 ρ`) and a 64-thread named barrier (`statsId st k = k + 3 + 4 st`, with
`k = w % 4` for softmax warp `w` and `k = w - 8` for correction warp `w`): the softmax warp
`bar.arrive`s after its store, the correction warp `bar.sync`s before its load. The correction
gives the slot back through stage `st`'s credit mbarrier (`statsBar`, offset `240 + 8 st`, count
128): every correction thread arrives on it after each load of the stage (and once before the
first), and the softmax polls it before each arrival on its named barrier.

The fields are event-level facts of single threads: what each role's run invariant
(`Softmax.Counts`, `Correction.Counts`) says about its barrier events, its credit polls and
arrivals and its accesses of the statistics words, plus the warp uniformity of named-barrier
events (all lanes of a warp follow the same sites with warp-uniform barrier operands). Every
ordinal is counted in the thread's own trace: `barOrd X g i id` is the number of `g`'s events on
named barrier `id` before its event `i`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- The named barrier of stage `st` between softmax warp `k + 4 st` and correction warp `8 + k`. -/
def statsId (st k : Nat) : Nat := k + 3 + 4 * st

/-- Stage `st`'s statistics credit mbarrier in CTA `c`. -/
def statsBar (L : Launch) (c st : Nat) : Loc := ⟨.shared, c, L.sharedBase + (240 + 8 * st)⟩

theorem statsBar_eq (L : Launch) (c : Nat) (st : Fin 2) :
    statsBar L c st = FBar.loc L c (.stats st) := rfl

/-- The key-value tiles of an item. -/
def kvTiles (L : Launch) : Nat := (skOf L + 127) / 128

/-- Value `v` is a canonical 4-byte single-precision word reading as `x`: the payload `x`, or a
32-bit pattern (no bit above bit 31, such as `0f3F800000`) that encodes `x`. -/
def F32Val (v : Value) (x : ℝ) : Prop :=
  (v = .float .f32 x ∨ ∃ b : BitVec 64, v = .bits 32 b ∧ b.toNat < 2 ^ 32) ∧
    valFloat .f32 v = .ok x

theorem F32Val.bytes_eq {v : Value} {x : ℝ} (h : F32Val v x) : v.bytes = 4 := by
  rcases h.1 with rfl | ⟨b, rfl, -⟩ <;> rfl

/-- The bytes `ws` of a store are those of a canonical single-precision word `v` reading as `x`
that rebuilds from them. -/
def F32Word (ws : List Byte) (x : ℝ) : Prop :=
  ∃ v, ws = v.toBytes ∧ rebuild 3 (ws.map some) = .ok v ∧ F32Val v x

/-- Read bytes `bs` rebuild to a canonical single-precision word reading as `x`. -/
def F32Read (bs : List (Option Byte)) (x : ℝ) : Prop :=
  ∃ v, rebuild 3 bs = .ok v ∧ F32Val v x

/-- A thread's row: its thread index modulo 128. -/
def rowOf (L : Launch) (g : Nat) : Nat := g % L.block % 128

theorem rowOf_lt (L : Launch) (g : Nat) : rowOf L g < 128 := Nat.mod_lt _ (by decide)

/-- The statistics word of row `ρ` of stage `st` in CTA `c`. -/
def statsWord (L : Launch) (c st ρ : Nat) : Loc :=
  ⟨.shared, c, L.sharedBase + (332 + 512 * st + 4 * ρ)⟩

/-- A byte of the statistics words of either stage, in some CTA. -/
def InStatsArea (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 332 ≤ l.addr ∧ l.addr < L.sharedBase + 1356

/-- The events on named barrier `id` of thread `g` before its event `i`. -/
def barOrd (X : Execution) (g i id : Nat) : Nat :=
  ((X.tr g).take i).countP (Execution.isBarId id)

/-- A softmax thread's access of a statistics word: a 4-byte store of its row's word of its stage,
with one more successful credit poll of the stage before it than its events on its named barrier
`w + 3`; the thread's next event, if it has one, is its `bar.arrive` on that barrier. -/
def SoftStore (L : Launch) (X : Execution) (g i : Nat) (a : Acc) (w : Bool) : Prop :=
  w = true ∧ a.loc = statsWord L (ctaOf L g) (warpOf L g / 4) (rowOf L g) ∧ a.size = 4 ∧
    okPolls (statsBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take i) =
      barOrd X g i (warpOf L g + 3) + 1 ∧
    (i + 1 < (X.tr g).length →
      ∃ pc, X.get (g, i + 1) = some ⟨pc, .bar (warpOf L g + 3) (some 64) .arrive⟩)

/-- A correction thread's access of a statistics word of stage `st`: a 4-byte load of its row's
word, after one more `bar.sync` on its barrier of the stage (`w - 5 + 4 st`) than its credit
arrivals of the stage; the last of those `bar.sync`s has ordinal `(n + 1) j + t + 1` with
`t < n` (a loop trip's or the last pass's, never the first one of an item). -/
def CorrLoad (L : Launch) (X : Execution) (g i : Nat) (a : Acc) (w : Bool) (st : Nat) : Prop :=
  w = false ∧ a.loc = statsWord L (ctaOf L g) st (rowOf L g) ∧ a.size = 4 ∧
    arrivals (statsBar L (ctaOf L g) st) ((X.tr g).take i) + 1 =
      barOrd X g i (warpOf L g - 5 + 4 * st) ∧
    ∃ j t, t < kvTiles L ∧ barOrd X g i (warpOf L g - 5 + 4 * st) = (kvTiles L + 1) * j + t + 2

/-- The thread layer's facts for the statistics handoff. -/
structure StatsFacts (L : Launch) (X : Execution) : Prop where
  /-- Named-barrier events: barrier 2 with 416 threads, or a statistics barrier with 64, on which
  softmax warp `w` only arrives (`bar.arrive` on `w + 3`) and correction warp `w` only waits
  (`bar.sync` on `w - 5` for stage 0, `w - 1` for stage 1). -/
  bar_form : ∀ {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    X.get (g, i) = some ⟨pc, .bar id cnt m⟩ → (id = 2 ∧ cnt = some 416) ∨
      (cnt = some 64 ∧ ((warpOf L g < 8 ∧ id = warpOf L g + 3 ∧ m = .arrive) ∨
        (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ (id = warpOf L g - 5 ∨ id = warpOf L g - 1) ∧
          m = .sync)))
  /-- The lanes of a warp make the same named-barrier events in the same order. -/
  bar_warp : NamedBar.WarpBars L X
  /-- A softmax thread's event on its statistics barrier follows one more successful poll of its
  stage's credit barrier than its earlier events on the statistics barrier. -/
  soft_credit : ∀ {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    warpOf L g < 8 → X.get (g, i) = some ⟨pc, .bar id cnt m⟩ → id ≠ 2 →
      okPolls (statsBar L (ctaOf L g) (warpOf L g / 4)) ((X.tr g).take i) = barOrd X g i id + 1
  /-- A correction thread's credit arrival of stage `st` follows one more `bar.sync` on its
  barrier of the stage than its earlier credit arrivals of the stage. -/
  corr_credit : ∀ {g i pc st tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope},
    g < L.threads → 8 ≤ warpOf L g → warpOf L g < 12 → st < 2 →
    X.get (g, i) = some ⟨pc, .arrive m tx cnt rel sc⟩ → m = statsBar L (ctaOf L g) st →
      arrivals m ((X.tr g).take i) + 1 = barOrd X g i (warpOf L g - 5 + 4 * st)
  /-- An arrival on a credit barrier is a correction thread's of the barrier's CTA: one release
  arrival without transaction bytes. -/
  credit_arrive : ∀ {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    st < 2 → X.get (g, i) = some ⟨pc, .arrive (statsBar L c st) tx cnt rel sc⟩ →
      8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true
  /-- A poll of a credit barrier is a softmax thread's of the barrier's CTA and stage, with the
  parity of its earlier successful polls of the barrier plus one; a successful one acquires. -/
  credit_poll : ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads →
    st < 2 → X.get (g, i) = some ⟨pc, .wait (statsBar L c st) p ok acq sc⟩ →
      warpOf L g < 8 ∧ warpOf L g / 4 = st ∧ c = ctaOf L g ∧
      p % 2 = (okPolls (statsBar L c st) ((X.tr g).take i) + 1) % 2 ∧ (ok = true → acq = true)
  /-- No tensor copy completes on a credit barrier. -/
  credit_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ statsBar L c st
  /-- No commit arrives on a credit barrier. -/
  credit_commit : ∀ {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}, st < 2 →
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp rank ≠ some (statsBar L c st)
  /-- Every access of a statistics byte is a softmax store or a correction load. -/
  stats_access : ∀ {g i : Nat} {a : Acc} {w : Bool} {l : Loc}, g < L.threads →
    X.Access (g, i) a w → a.Covers l → InStatsArea L l →
      (warpOf L g < 8 ∧ SoftStore L X g i a w) ∨
        (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ ∃ st < 2, CorrLoad L X g i a w st)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
