-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.Sites

@[expose] public section

/-!
# The matrix sites of a tile, by ordinal

A compute lane makes 182 warp matrix events per tile; the *ordinal* of an event is its number
(0 to 181) in the tile. `MSite` names the site of the thread machine at which a lane performs
its matrix event: the second event of an `ldmatrix` (after its row read), an `mma.sync`, a
`movmatrix`, or the first event of an `stmatrix` (before its row write). The generated table
`ordSite` (`Proof/Values/Gen/Sites.lean`) gives the site of each ordinal.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX.Kernels.FlashKdaFwd.Proof.Thread

/-- The site of a matrix event: its kind and its ordinal among the sites of that kind. -/
inductive MSite where
  /-- The matrix event of the `j`-th `ldmatrix` (its second event). -/
  | load (j : Fin 44)
  /-- The `j`-th `mma.sync`. -/
  | mma (j : Fin 104)
  /-- The `j`-th `movmatrix`. -/
  | move (j : Fin 16)
  /-- The matrix event of the `j`-th `stmatrix` (its first event). -/
  | store (j : Fin 18)
  deriving DecidableEq, Repr

/-- The machine is at the matrix site `m`. -/
def MSite.At : MSite → Site → Prop
  | .load j, s => ∃ row, s = .matrixLoadMx j row
  | .mma j, s => s = .warpMma j
  | .move j, s => s = .matrixMove j
  | .store j, s => s = .matrixStore j

/-- **A program point of a compute lane inside a tile**: a site of the thread machine at which
the lane waits for an event of the tile's data path. Besides the four matrix sites these are
the first event of an `ldmatrix` (its row read), the second event of an `stmatrix` (its row
write) and the scalar loads of the tile loop (two gate logits, sixteen entries of `g_total`). -/
inductive Pt where
  /-- Before the row read of the `j`-th `ldmatrix`. -/
  | rd (j : Fin 44)
  /-- Before the matrix event of the `j`-th `ldmatrix`, holding the row it read. -/
  | mx (j : Fin 44)
  /-- Before the `j`-th `mma.sync`. -/
  | mma (j : Fin 104)
  /-- Before the `j`-th `movmatrix`. -/
  | mov (j : Fin 16)
  /-- Before the matrix event of the `j`-th `stmatrix`. -/
  | st (j : Fin 18)
  /-- Before the row write of the `j`-th `stmatrix`, holding the row it received. -/
  | wr (j : Fin 18)
  /-- Before the scalar load at the machine's load site `i`. -/
  | ld (i : Fin 178)
  deriving DecidableEq, Repr

/-- The point at which a lane makes the matrix event of the matrix site `m`. -/
def Pt.ofMSite : MSite → Pt
  | .load j => .mx j
  | .mma j => .mma j
  | .move j => .mov j
  | .store j => .st j

end PTX.Kernels.FlashKdaFwd.Proof.Values
