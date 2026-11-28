-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-! # What a query half is

Half `j` of lane `tid` is the element of the query tensor at the row `qTileRow tid (j / 16)` of
the tile (token `row / 6`, head `6 y + row % 6` of the CTA's head block) and the column `qDim`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- The tile row of the group `gp` of lane `tid`. -/
def qTileRow (tid gp : Nat) : Nat := tid / 8 % 16 + 16 * gp

/-- The query element at tile row `row` and column `d` of the CTA `c`. -/
noncomputable def qMat (Q : Params) (L : Launch) (c row d : Nat) : ℝ :=
  Q.q (Q.qStart ((L.ctaidOf c).get .z) + row / 6) ((L.ctaidOf c).get .y * 6 + row % 6) d

/-- The column of half `j` of lane `tid`. -/
def qDim (tid j : Nat) : Nat := 8 * (tid % 8) + j % 16 % 8 + 64 * (j % 16 / 8)

/-- The element half `j` of thread `g` holds. -/
noncomputable def qElem (Q : Params) (L : Launch) (g j : Nat) : ℝ :=
  qMat Q L (g / L.block) (qTileRow (g % L.block) (j / 16)) (qDim (g % L.block) j)

/-- **A row loads**: it is a row of the tile and its token is a valid token of the request. -/
def QRowValid (Q : Params) (L : Launch) (c row : Nat) : Prop :=
  row < 60 ∧ row / 6 < Q.qLen ((L.ctaidOf c).get .z)

/-- **A row group loads.** -/
def QValid (Q : Params) (L : Launch) (g gp : Nat) : Prop :=
  QRowValid Q L (g / L.block) (qTileRow (g % L.block) gp)

end PTX.Kernels.InklingRelDecode.Proof.Lib
