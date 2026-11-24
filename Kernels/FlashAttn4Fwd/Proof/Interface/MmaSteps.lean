-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Score

@[expose] public section

/-! # What the thread layer exports for the K steps of the MMAs

The MMA thread issues each score tile of a stage as one block of eight QK MMAs (asm blocks S0,
S1: `tcgen05.mma … fa_fwd_q_smem_desc_j, smem_desc_b_j, …, j ≠ 0`) and each PV tile as one block
of eight PV MMAs (`[tmem_a + 8 j]`, enable-input-D `p` at `j = 0` and `1` after). The K step of an
MMA is its number in its block, counted along the thread: `qkStep` counts the earlier MMAs of the
thread writing the stage's scores after as many commits to the stage's S-full object, `pvStep`
the earlier ones writing the stage's accumulator after as many polls of its P-ready object.

The fields are facts of the MMA thread, from its run invariant (`Mma.Counts`: one block per tile,
eight MMAs per block, no commit or P-ready poll of the stage inside a block) and the constants of
its MMA sites (`Mma.asmVals`):

* **QK steps** (`qk_step`): a QK MMA is step `j < 8` of its block; step 0 does not accumulate.
* **PV steps** (`pv_step`): a PV MMA is step `j < 8` of its block; it does not accumulate exactly
  at step 0 of the first tile of an item (`pPolls - 1 ≡ 0 mod n`, the trip predicate `t ≠ 0`).
* **PV blocks are whole** (`pv_next`): a PV MMA of step `j < 7` is followed, before any later PV
  MMA of the stage of a later tile, by a PV MMA of its tile.
* **P columns** (`pv_a`): PV step `j` of stage `st` reads its A operand from Tensor Memory at
  column `128 st + 64 + 8 j` (`[tmem_a + 8 j]`, `tmem_a` = 64 or 192). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- Event `k` of thread `g` is an MMA writing stage `st`'s scores. -/
def QkAt (X : Execution) (g st k : Nat) : Prop :=
  IsMma X (g, k) ∧ ∃ cell, X.MmaCell (g, k) cell ∧ InS st cell

/-- Event `k` of thread `g` is an MMA writing stage `st`'s accumulator. -/
def PvAt (X : Execution) (g st k : Nat) : Prop :=
  IsMma X (g, k) ∧ ∃ cell, X.MmaCell (g, k) cell ∧ InO st cell

open Classical in
/-- The K step of event `k` of thread `g` among stage `st`'s QK MMAs: the earlier ones after as
many commits to the stage's S-full object. -/
def qkStep (L : Launch) (X : Execution) (g st k : Nat) : Nat :=
  ((Finset.range k).filter fun k' =>
    QkAt X g st k' ∧ sCommits L X g st k' = sCommits L X g st k).card

open Classical in
/-- The K step of event `k` of thread `g` among stage `st`'s PV MMAs: the earlier ones after as
many polls of the stage's P-ready object. -/
def pvStep (L : Launch) (X : Execution) (g st k : Nat) : Nat :=
  ((Finset.range k).filter fun k' =>
    PvAt X g st k' ∧ pPolls L X g st k' = pPolls L X g st k).card

/-- The thread layer's facts for the K steps of the MMAs. -/
structure MmaStepFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- A QK MMA is one of the eight steps of its block; step 0 overwrites. -/
  qk_step : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    {st : Nat}, st < 2 → X.MmaIssue i d s acc mask → X.MmaCell i cell → InS st cell →
      qkStep L X i.1 st i.2 < 8 ∧ (acc = false → qkStep L X i.1 st i.2 = 0)
  /-- A PV MMA is one of the eight steps of its block; it overwrites exactly at step 0 of the
  first tile of an item. -/
  pv_step : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    {st : Nat}, st < 2 → X.MmaIssue i d s acc mask → X.MmaCell i cell → InO st cell →
      pvStep L X i.1 st i.2 < 8 ∧ (acc = false ↔
        pvStep L X i.1 st i.2 = 0 ∧ (pPolls L X i.1 st i.2 - 1) % kvBlocks P = 0)
  /-- A PV MMA of step `j < 7` is followed by a PV MMA of its tile before a later tile's. -/
  pv_next : ∀ {g st k k' : Nat}, st < 2 → PvAt X g st k → pvStep L X g st k < 7 → PvAt X g st k' →
    k < k' → pPolls L X g st k < pPolls L X g st k' →
      ∃ k'', k < k'' ∧ k'' < k' ∧ PvAt X g st k'' ∧ pPolls L X g st k'' = pPolls L X g st k
  /-- PV step `j` of stage `st` reads A from Tensor Memory column `128 st + 64 + 8 j`. -/
  pv_a : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    {st : Nat}, st < 2 → X.MmaIssue i d s acc mask → X.MmaCell i cell → InO st cell →
      ∃ address, s.aTmem = some address ∧
        address % 2 ^ 16 = 128 * st + 64 + 8 * pvStep L X i.1 st i.2

end
end PTX.Kernels.FlashAttn4Fwd.Proof
