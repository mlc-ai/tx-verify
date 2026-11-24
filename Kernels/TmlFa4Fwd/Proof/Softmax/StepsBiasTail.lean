-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPwE2
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A bias round's loop tail after the row sum -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 addi xor32 scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The closing wait's state. -/
abbrev pwB (v : V) : D := D.mk' (.pwend .bias) v

/-- The control keys live after the bias sum. -/
def ctlBE : List Nat :=
  [441, 1062, 1069, 1215, 1229, 1359, 1361, 2390, 2535, 5127, 6495, 6497, 7132, 7248, 7249,
   7250, 7253, 7258, 7500, 7501, 7502, 7503, 7506, 7896]

/-- The facts carried across the sum and used by the loop tail. -/
abbrev pwBH (p : Params) (L : Launch) (g : Nat) (v : V) (M : Value) : List (Nat × Value) :=
  (7256, M) :: (1230, negS p) :: factsFrom ctlBE (valueOf p L g (pwB v))

/-- The loop-tail control state with the completed row statistics. -/
def biasTailV (v : V) (b : Bool) (r x : ℝ) : V :=
  { v with
    mf := b, mr := r, rs := x, nb := addi v.nb 1,
    ppar := xor32 v.ppar (i32 1), bpar := xor32 v.bpar (i32 1), spar := xor32 v.spar (i32 1) }


/-- The updated control and statistics at the bias loop's back-edge branch. -/
def pwBBranch (p : Params) (L : Launch) (g : Nat) (v : V) (b : Bool) (r x : ℝ) :
    List (Nat × Value) :=
  (642, .pred (scmpi .ne .b (addi v.nb 1) (-1))) ::
    (7251, mxVal (biasTailV v b r x)) :: (7257, .float .f32 x) ::
    pwBH p L g (biasTailV v b r x) (mxVal (biasTailV v b r x))


end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
