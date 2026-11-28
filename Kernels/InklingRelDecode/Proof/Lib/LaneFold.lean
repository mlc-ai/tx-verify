-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Lib.PvFold
public import Kernels.InklingRelDecode.Proof.Lib.SoftLane

@[expose] public section

/-! # The fold of the lane's row

The fold's state after `n` blocks and the block of round `n` for the row of a thread, in the
kernel's domain. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- The fold's state of the lane's row after `n` blocks. -/
noncomputable def laneSt (Q : Params) (L : Launch) (g n : Nat) : Lib.SoftFold.St :=
  Lib.SoftRow.kSt Q ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
    (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) 0 n

/-- The lane's block of the round `n`. -/
noncomputable def laneBlk (Q : Params) (L : Launch) (g n : Nat) : List (ℝ × ℝ) :=
  Lib.SoftRow.kBlk Q ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)
    (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) 0 n

theorem laneSt_succ (Q : Params) (L : Launch) (g n : Nat) :
    laneSt Q L g (n + 1) =
      SoftFold.step (Q.scale * log2eF32) (laneBlk Q L g n) (laneSt Q L g n) :=
  Lib.SoftRow.kSt_succ _ _ _ _ _ _ _

theorem laneSt_zero (Q : Params) (L : Launch) (g : Nat) : (laneSt Q L g 0).m = ⊥ := rfl

/-- **The probability word of column `c` of the lane's half in round `i`**: the exponential of
the visible key's score relative to the maximum the round uses, zero for a key not seen. -/
noncomputable def lanePw (Q : Params) (L : Launch) (g i c : Nat) : ℝ :=
  if laneKey Q L g i c ≤ Q.past ((L.ctaidOf (g / L.block)).get .z) + softRow (g % L.block) / 6 then
    pExp (Q.scale * log2eF32) (mUseOf (Q.scale * log2eF32) (laneBlk Q L g i) (laneSt Q L g i))
      (laneBias Q L g i c * (1 / Q.scale) + laneScore Q L g i c, 0)
  else 0

end PTX.Kernels.InklingRelDecode.Proof.Lib
