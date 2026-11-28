-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.PwEx
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal6

@[expose] public section

/-! # The row sum register is the sum of the lane's half of the probabilities

At the exponent window's result the row sum (register 1529) is the sum, over the 64 columns of the
lane's half of the round's block, of the exact probabilities. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Data

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

theorem xRegs_eq : xRegs = (List.range 64).map (fun u => 1288 + 2 * u) := by decide +kernel

theorem sum_range_map (f : Nat → ℝ) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- **The row sum is the sum of the half's probabilities.** -/
theorem row_sum_word {y : Data.D} (hpos : 0 < Q.scale * log2eF32)
    (hE : ExpInX (xV ent L g y) (regX Q L g y.c.i) (Q.scale * log2eF32)
      (Lib.mUseOf (Q.scale * log2eF32) (Lib.laneBlk Q L g y.c.i) (Lib.laneSt Q L g y.c.i) *
        (-(Q.scale * log2eF32)))) :
    vE3 (xV ent L g y) 1529 =
      .float .f32 (∑ c ∈ Finset.range 64, Lib.lanePw Q L g y.c.i c) := by
  rw [(exp_exact hE).2, xRegs_eq, List.map_map]
  congr 1
  rw [Function.comp_def, sum_range_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  have e1 : regX Q L g y.c.i (srcTab j) = Lib.colX Q ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g)
      y.c.i (64 * (g % L.block / 16 % 2) + j) := by
    unfold regX; rw [colOfSrc_srcTab _ (Finset.mem_range.mp hj)]
  unfold shifted
  rw [show (1288 + 2 * j - 1288) / 2 = j by omega, e1, pw2_col Q L g _ _ hpos]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
