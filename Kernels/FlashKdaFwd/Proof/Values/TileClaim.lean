-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Induction
public import Kernels.FlashKdaFwd.Proof.Values.TileInputs

@[expose] public section

/-!
# The conclusion of the induction over the tiles, as a statement

This file only STATES what the value induction delivers (`TileClaim`) and what it takes from
outside (`TileHyps`), so that the layers above can be built on the claim while the induction
is being proved. `TileInduction` is the statement "the hypotheses give the claim".

Words. A *compute warp* of thread block `c` (`c < L.grid`) is its warp number `w < 4`; its
first thread is `c * L.block + 32 * w` and its lane `l < 32` is the thread
`g = c * L.block + 32 * w + l`. `stateAt (code L) X g k` is the state of the machine of thread
`g` before event `k` of its trace (a *followed* state when it is `some (some d)`), and
`ordinal X g k` the number of warp matrix events before it: the lane is in tile
`ordinal / 182`, having made `ordinal % 182` matrix events of that tile. The real arrays of
tile `b` of block `c` are `blockInputs P mem0 c b` (`tileInputs` for the block's sequence
`c % P.sequences` and head `c / P.sequences`).

`TileClaim` has four fields.

* `val`: the invariant `Val` of `Induction.lean` for every compute warp and every number of
  matrix events. For a followed state `d` of a lane with `N` matrix events it says (`Inv`): the
  lane is at one of the program points of count `N % 182` (`pointsAt`) and its data slots `d.x`
  satisfy the table of that point on the arrays of tile `N / 182` (`SiteOk`; at the second
  event of a load or a store the row it holds is the row of the arrays); or, when `N % 182 = 0`,
  it is in the tail of the tile before (`TailOk`: its carries satisfy the table of ordinal 0 on
  the arrays of tile `N / 182`), or it has left the loop (`Left`), or it has not entered it
  (`N = 0`, `¬ Entered`). When `N % 182 ≠ 0` only the first case remains (`TileClaim.inside`).
* `matrix`: at a matrix site (the second event of an `ldmatrix`, an `mma.sync`, a `movmatrix`,
  the first event of an `stmatrix`) a lane whose state satisfies `SiteOk` makes a matrix event
  and nothing else.
* `alive`: a lane whose state satisfies `SiteOk`, or is at the row write of the last store of
  a tile with `TailOk`, has a followed state after its next event (no instruction of the data
  path faults: this is where the conditions of the runs of scalar instructions are proved).
* `mma`: the operands of every multiply-accumulate instance of a compute warp are real
  matrices (`WarpMatrix.Operands`), in the form of `DirectFacts.mmaOperands`.

Derived here from `val`: `TileClaim.inside`, and `TileClaim.exit` (at the first position at
which a lane is at the site after the exit branch of the loop, `Site.bar 7`, with `182 * b`
matrix events, `b ≥ 1`, its carries satisfy the table of ordinal 0 on the arrays of entry `b`
of the family: for `b` the tile count these are the final state, `tileInputs_last`).

`TileHyps` lists the hypotheses: the launch precondition, the three contracts of
`Contract.lean`, those of `Hyps.lean`, and `early` (no 16-byte write of a lane before its first
matrix event). The rows the loads read are derived inside the induction: the reads of the
input stage from the contracts (`StageReads.lean: rows_read_stage`), the rows of `state_acc`
from the protocol layer's read-back `ReadBack.acc` and the lane's own row writes of the tile
before (`AccRows.lean: acc_rows`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments

noncomputable section

/-- The real arrays of tile `b` of thread block `c`. -/
def blockInputs (P : Params) (mem0 : Mem0) (c b : ℕ) : Inputs :=
  tileInputs P mem0 (c % P.sequences) (c / P.sequences) b

/-- **What the induction over the tiles delivers.** -/
structure TileClaim (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  /-- The invariant, for every compute warp and every number of matrix events. -/
  val : ∀ c w, c < L.grid → w < 4 → ∀ N,
    Val (L := L) (blockInputs P mem0 c) w X (c * L.block + 32 * w) N
  /-- At a matrix site only a matrix event occurs. -/
  matrix : ∀ c w, c < L.grid → w < 4 → ∀ l < 32, ∀ k d e,
    stateAt (code L) X (c * L.block + 32 * w + l) k = some (some d) →
    X.get (c * L.block + 32 * w + l, k) = some e →
    SiteOk (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182)) w l
      (ordinal X (c * L.block + 32 * w + l) k % 182) d →
    ((∃ j row, d.site = .matrixLoadMx j row) ∨ (∃ j, d.site = .warpMma j) ∨
      (∃ j, d.site = .matrixMove j) ∨ ∃ j, d.site = .matrixStore j) →
    isMatrix e = true
  /-- The state after the next event of a lane at a program point is followed. -/
  alive : ∀ c w, c < L.grid → w < 4 → ∀ l < 32, ∀ k d e,
    stateAt (code L) X (c * L.block + 32 * w + l) k = some (some d) →
    X.get (c * L.block + 32 * w + l, k) = some e →
    (SiteOk (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182)) w l
        (ordinal X (c * L.block + 32 * w + l) k % 182) d ∨
      (ordinal X (c * L.block + 32 * w + l) k % 182 = 0 ∧
        1 ≤ ordinal X (c * L.block + 32 * w + l) k / 182 ∧
        (∃ row, d.site = .matrixStoreWr 17 row) ∧
        TailOk (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182 - 1))
          (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182)) w l d)) →
    ∃ d', stateAt (code L) X (c * L.block + 32 * w + l) (k + 1) = some (some d')
  /-- The operands of the multiply-accumulates of a compute warp. -/
  mma : ∀ c w, c < L.grid → w < 4 → ∀ n pc s parts,
    WarpInstance X (c * L.block + 32 * w) n pc (.mma s) parts →
    s = mma16 ∧ ∃ ra rb rc a b c', Operands ra rb rc a b c' ∧
      ∀ l < 32, parts l = mmaParts ra rb rc l

/-- **What the induction takes from outside.** -/
structure TileHyps (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop where
  pre : Pre P L mem0
  followed : Followed L mem0 X
  ref : ComputeRef P L X
  back : ReadBack P L mem0 X
  exit : LoopExit P L X
  bound : TileBound P L X
  /-- Every compute warp is a warp: its first thread has lane 0 and its lanes are compute
  threads (a fact of the launch shape). -/
  warp : ∀ c w, c < L.grid → w < 4 → Warp L (c * L.block + 32 * w)
  base : ∀ c w, c < L.grid → w < 4 →
    Base (L := L) (blockInputs P mem0 c) w X (c * L.block + 32 * w)
  first : ∀ c w, c < L.grid → w < 4 → FirstLoad (L := L) X (c * L.block + 32 * w)
  /-- A compute lane makes no 16-byte write before its first matrix event (the conversion loop
  of the prologue writes two bytes at a time): the rows of `state_acc` that the first tile reads
  still hold the converted initial state. -/
  early : ∀ c w, c < L.grid → w < 4 → ∀ l < 32, ∀ k pc a bs,
    ordinal X (c * L.block + 32 * w + l) k = 0 →
    X.get (c * L.block + 32 * w + l, k) = some ⟨pc, .wr a bs⟩ → a.size ≠ 16

/-- **The statement of the induction over the tiles.** -/
def TileInduction (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop :=
  TileHyps P L mem0 X → TileClaim P L mem0 X

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Inside a tile** (a number of matrix events that is no multiple of 182) a followed state
of a compute lane is at a program point of its count and satisfies it. -/
theorem TileClaim.inside (C : TileClaim P L mem0 X) {c w l : ℕ} (hc : c < L.grid) (hw : w < 4)
    (hl : l < 32) {k : ℕ} {d : D}
    (hσ : stateAt (code L) X (c * L.block + 32 * w + l) k = some (some d))
    (hn : ordinal X (c * L.block + 32 * w + l) k % 182 ≠ 0) :
    SiteOk (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182)) w l
      (ordinal X (c * L.block + 32 * w + l) k % 182) d := by
  rcases C.val c w hc hw _ l hl k rfl d hσ with h | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  · exact absurd h0 hn
  · exact absurd h0 hn
  · exact absurd (by omega) hn

/-- No program point of a tile is at a `bar.sync`. -/
theorem Pt.not_shape_bar {pt : Pt} {j : Fin 10} : ¬ pt.Shape (.bar j) := by
  intro h
  cases pt <;> first | (obtain ⟨_, h'⟩ := h; cases h') | cases h

/-- **At the exit of the loop.** A compute lane that is at the site after the exit branch
(`Site.bar 7`) with `182 * b` matrix events, `b ≥ 1`, was at that site at a first position `k'`
with the same count, and there its data slots satisfy the table of ordinal 0 (the 128 carries)
on the arrays of entry `b` of the family. -/
theorem TileClaim.exit (C : TileClaim P L mem0 X) {c w l : ℕ} (hc : c < L.grid) (hw : w < 4)
    (hl : l < 32) : ∀ k d, stateAt (code L) X (c * L.block + 32 * w + l) k = some (some d) →
    d.site = .bar 7 → 1 ≤ ordinal X (c * L.block + 32 * w + l) k / 182 →
    ∃ k' ≤ k, ∃ d', stateAt (code L) X (c * L.block + 32 * w + l) k' = some (some d') ∧
      d'.site = .bar 7 ∧
      ordinal X (c * L.block + 32 * w + l) k' = ordinal X (c * L.block + 32 * w + l) k ∧
      (tableAt 0).Holds
        (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182)) w l d'.x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hσ hs h1
    rcases C.val c w hc hw _ l hl k rfl d hσ with
      ⟨q, -, hat, -⟩ | ⟨-, -, -, ht⟩ | ⟨-, -, k', hk', ho, d', hσ', hs'⟩ | ⟨h0, -⟩
    · exact absurd (hs ▸ hat.shape) Pt.not_shape_bar
    · exact ⟨k, le_rfl, d, hσ, hs, rfl, ht⟩
    · obtain ⟨k'', hk'', d'', hσ'', hs'', ho'', hT''⟩ := ih k' hk' d' hσ' hs' (by rw [ho]; exact h1)
      exact ⟨k'', by omega, d'', hσ'', hs'', ho''.trans ho, by rw [← ho]; exact hT''⟩
    · omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
