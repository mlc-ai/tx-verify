-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-! # What a softmax lane works on

The thread `t` of a CTA takes the row `t % 16 + t / 32 % 4 * 16` of the score tile (token
`row / 6`, head `row % 6` of the CTA's head group) and the 64 columns from `t / 16 % 2 * 64` of each
block. In round `i` the block is `splits * i + x`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- The row of the score tile of the thread `t` of a CTA. -/
def softRow (t : Nat) : Nat := t % 16 + t / 32 % 4 * 16

/-- The key of the column `j` of the thread's half in round `i`. -/
def laneKey (Q : Params) (L : Launch) (g i j : Nat) : Nat :=
  128 * (Q.splits * i + (L.ctaidOf (g / L.block)).get .x) + 64 * (g % L.block / 16 % 2) + j

/-- The head of the thread's row. -/
def laneHead (L : Launch) (g : Nat) : Nat :=
  (L.ctaidOf (g / L.block)).get .y * 6 + softRow (g % L.block) % 6

/-- The specification's score of the thread's row and the key of column `j` in round `i`. -/
noncomputable def laneScore (Q : Params) (L : Launch) (g i j : Nat) : ℝ :=
  score Q ((L.ctaidOf (g / L.block)).get .z) (softRow (g % L.block) / 6) (laneHead L g)
    (laneKey Q L g i j)

/-- The specification's bias of the same. -/
noncomputable def laneBias (Q : Params) (L : Launch) (g i j : Nat) : ℝ :=
  bias Q ((L.ctaidOf (g / L.block)).get .z) (softRow (g % L.block) / 6) (laneHead L g)
    (laneKey Q L g i j)

end PTX.Kernels.InklingRelDecode.Proof.Lib
