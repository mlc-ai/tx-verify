-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Step

@[expose] public section

/-!
# What the induction over a tile assumes

The value induction (`Induction.lean`, `Tile.lean`) follows a compute lane through the tile
loop. Besides the three contracts of `Contract.lean` it takes the hypotheses of this file. Each
is about the lanes of one compute warp (first thread `w0`, warp number `w`) and the family `xs`
of the real arrays of each tile (`xs b : Math.Fragments.Inputs`). A *position* `k` of a lane's
trace is the index of an event; `stateAt (code L) X g k` is the state of the lane's machine
before that event, and `ordinal X g k` the number of warp matrix events before it (so
`ordinal / 182` is the tile the lane is in).

* `RowsRead`: the row a lane reads at the first event of an `ldmatrix` is the row of the load's
  source for the arrays of its tile (`LoadSrc.RowOk`).
* `ScalarsRead`: the bytes a lane reads at a scalar load of the tile loop (a gate logit or an
  entry of `g_total`; the machine's load sites 159 to 176) are those of its tile
  (`ScalarSrc.Bytes`).
  Both follow from the reference layer's footprints (`ComputeRef.loadRow`, `scalarLoad`,
  `polled`) and the protocol layer's read-back (`ReadBack`).
* `Base`: when a lane arrives at the first `ldmatrix` of the first tile, its 128 carry
  registers hold the initial FP32 state (the table of ordinal 0 on the arrays of tile 0). This
  is the base case, proved with the prologue of the kernel.
* `FirstLoad`: the machine reaches the second event of the first `ldmatrix` only from its first
  event (a fact about the transitions of the generated machine).
* `TileBound`: a lane at a read of the input stage (the first event of an `ldmatrix`, a scalar
  load) is in a tile of its sequence (from the reference layer of the Compute phase); it is
  used to read the workspace arrays of the tile off the launch precondition.
* `LoopExit`: a lane that is at the `bar.sync` after the exit branch of the tile loop
  (`Site.bar 7`) has made all `182 * tiles` matrix events of its sequence (from the reference
  layer of the Compute phase: the exit is taken when the tile counter reaches the tile count).

The file also names the generated lists as functions: `storeSrc`, `scalarSrc`, `pointsAt`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments

noncomputable section

variable {P : Params} {L : Launch} {X : Execution}

/-- What the `j`-th `stmatrix` of a tile writes. -/
def storeSrc (j : ℕ) : StoreSrc := Gen.storeSrcs.getD j (.out 0)

/-- What the scalar load at the machine's load site `i` (159 to 176) reads. -/
def scalarSrc (i : ℕ) : ScalarSrc := Gen.scalarSrcs.getD (i - 159) (.logit 0)

/-- The program points of a lane that has made `n` matrix events of its tile, each with the
table of its data registers (for `n = 0`: the two points of the first load only). -/
def pointsAt (n : ℕ) : List (Pt × Table) := Gen.points.getD n []

/-- **The rows the loads read**: the read event of a lane at the first event of the `j`-th
`ldmatrix` returns a row of the load's source, for the arrays of the lane's tile. -/
def RowsRead (xs : ℕ → Inputs) (w : ℕ) (X : Execution) (w0 : ℕ) : Prop :=
  ∀ l < 32, ∀ k d e (j : Fin 44),
    stateAt (code L) X (w0 + l) k = some (some d) → d.site = .matrixLoad j →
    X.get (w0 + l, k) = some e →
    ∃ pc a row, e = ⟨pc, .rd a row⟩ ∧
      (loadSrc j).RowOk (xs (ordinal X (w0 + l) k / 182)) w l row

/-- **The bytes the scalar loads read**: the read event of a lane at a scalar load of the tile
loop returns the bytes of the load's source, for the arrays of the lane's tile. -/
def ScalarsRead (xs : ℕ → Inputs) (X : Execution) (w0 : ℕ) : Prop :=
  ∀ l < 32, ∀ k d e (i : Fin 178), 159 ≤ i.val → i.val < 177 →
    stateAt (code L) X (w0 + l) k = some (some d) → d.site = .load i →
    X.get (w0 + l, k) = some e →
    ∃ pc a bs, e = ⟨pc, .rd a bs⟩ ∧
      (scalarSrc i).Bytes (xs (ordinal X (w0 + l) k / 182)) l bs

/-- **The base case**: at the first `ldmatrix` of the first tile the data registers of a lane
(its 128 carries) satisfy the table of ordinal 0 on the arrays of tile 0. -/
def Base (xs : ℕ → Inputs) (w : ℕ) (X : Execution) (w0 : ℕ) : Prop :=
  ∀ l < 32, ∀ k d, ordinal X (w0 + l) k = 0 →
    stateAt (code L) X (w0 + l) k = some (some d) → d.site = .matrixLoad 0 →
    (tableAt 0).Holds (xs 0) w l d.x

/-- **The second event of the first `ldmatrix` follows its first event**: when event `k` of a
lane exists and the state after it is at the second event of the first `ldmatrix`, the state
before it is at the first event. -/
def FirstLoad (X : Execution) (w0 : ℕ) : Prop :=
  ∀ l < 32, ∀ k e d row, X.get (w0 + l, k) = some e →
    stateAt (code L) X (w0 + l) (k + 1) = some (some d) → d.site = .matrixLoadMx 0 row →
    ∃ d0, stateAt (code L) X (w0 + l) k = some (some d0) ∧ d0.site = .matrixLoad 0

/-- **A read of the input stage is in a tile of the sequence**: at the first event of an
`ldmatrix` and at a scalar load of the tile loop the lane's tile is below the tile count (from
the reference layer of the Compute phase: the lane is inside the loop). -/
def TileBound (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d, g % L.block < 128 → stateAt (code L) X g k = some (some d) →
    ((∃ j : Fin 44, d.site = .matrixLoad j) ∨
      ∃ i : Fin 178, 159 ≤ i.val ∧ i.val < 177 ∧ d.site = .load i) →
    ordinal X g k / 182 < tileCount P L g

/-- **A lane that has left the tile loop has made all its matrix events.** -/
def LoopExit (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d, g % L.block < 128 → stateAt (code L) X g k = some (some d) → d.site = .bar 7 →
    ordinal X g k = 182 * tileCount P L g

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
