-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.TmemDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutDefs
public import Lemmas.Flow.Polls

@[expose] public section

/-! # A consumer warp's warp-collective `tcgen05` events

The warp-collective `tcgen05` events of the kernel are made by the consumer warps: per tile, the
sixteen Tensor Memory loads of the warp's accumulator rows, each followed by its wait; and in
warp 0 the paired allocation (in the prologue), relinquishment and deallocation (at the exit).
Each is at a position `p` of the warp's sequence (`tcCollPc`, `TcCollKind`): `2 j` and `2 j + 1`
the load `j` and its wait, `32 + n` the `n`-th paired operation. A thread's collective events
before one at position `p` count its tiles: its successful response polls, one per tile
(`TcCollAt`); before the exit operations and the exit, its latest response read claims no CTA
(`NcRead`), and every earlier one claims a CTA (`NcLast`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Flow

noncomputable section

/-- A thread's successful polls of its CTA's response barrier. -/
abbrev respPolls (L : Launch) (g : Nat) (es : List Event) : Nat :=
  okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) es

/-- The source line at position `p` of a consumer warp's collective sequence. -/
def tcCollPc (p : Nat) : Nat :=
  if p < 32 then
    (if p % 2 = 0 then Flow.tmemLoad.getD (p / 2) 0 else Flow.tmemWait.getD (p / 2) 0)
  else tmemPc (p - 32)

/-- The event at position `p` of thread `g`'s collective sequence: the load of its warp group's
accumulator columns at chunk `p / 2`, its wait; the allocation of all columns into the CTA's base
word, the relinquishment, a deallocation of all columns. -/
def TcCollKind (L : Launch) (g p : Nat) (kd : TcKind) : Prop :=
  if p < 32 then
    (if p % 2 = 0 then ∃ vals, kd = .ld (256 * (g % L.block / 32 / 4) + 16 * (p / 2)) vals .s32x32b
     else kd = .waitLd)
  else if p = 32 then
    kd = .resource .two (some ⟨.shared, g / L.block, L.sharedBase⟩) (.alloc 512)
  else if p = 33 then kd = .resource .two none .relinquish
  else p = 34 ∧ ∃ a, kd = .resource .two none (.dealloc a 512)

/-- A read of the CTA's response right after the successful response poll at `j`, naming `rr`. -/
def RespRead (L : Launch) (g : Nat) (es : List Event) (j : Nat) (rr : ClcResponse) : Prop :=
  ∃ pc p acq sc pcr src bs, es[j]? =
    some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
    es[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
    src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
        false⟩ ∧
    Flow.responseOf bs = some rr

/-- Every response read that claims no CTA is after the latest successful response poll. -/
def NcLast (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∀ j rr, RespRead L g es j rr → ¬ Loader.claims rr →
    respPolls L g (es.take j) + 1 = respPolls L g es

/-- A response read after the latest successful response poll claims no CTA. -/
def NcRead (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∃ j rr, RespRead L g es j rr ∧ respPolls L g (es.take j) + 1 = respPolls L g es ∧
    ¬ Loader.claims rr

/-- The collective events before one at position `p`: before the allocation none; before a load
or its wait, the tiles before the current one, its position, and warp 0's allocation; before the
exit operations, every tile and warp 0's operations before them. -/
def TcCollAt (L : Launch) (g p : Nat) (es : List Event) : Prop :=
  (p < 32 → 1 ≤ respPolls L g es ∧
    es.countP isTcColl + 32 = (if g % L.block / 32 = 0 then 1 else 0) + 32 * respPolls L g es + p) ∧
  (32 ≤ p → g % L.block / 32 = 0) ∧
  (p = 32 → es.countP isTcColl = 0) ∧
  (33 ≤ p → es.countP isTcColl + 32 = 32 * respPolls L g es + p ∧ NcRead L g es) ∧
  (p ≠ 32 → NcLast L g es)

/-- The collective events before a consumer's exit: every tile, and warp 0's three operations;
its latest response read claims no CTA. -/
def TcExitAt (L : Launch) (g : Nat) (es : List Event) : Prop :=
  es.countP isTcColl = (if g % L.block / 32 = 0 then 3 else 0) + 32 * respPolls L g es ∧
    NcRead L g es

end

end PTX.Kernels.Fp16Gemm8192.Proof
