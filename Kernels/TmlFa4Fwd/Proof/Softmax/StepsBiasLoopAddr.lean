-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTail
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias back edge prepares its address registers -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 addi xor32 scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def loopInputs : List Nat := [1062, 2535, 7249]

def loopWritten : List Nat :=
  [631, 632, 3964, 3970, 3971, 3972, 3973, 3976, 3977, 3982, 3986, 3990, 3994, 3998, 4002,
   4006, 4010, 4014, 4018, 4022, 4026, 4030, 4034, 4037, 7249]

def loopCarried : List Nat := ctlBE.filter (!loopWritten.contains ·)

abbrev loopInput (L : Launch) (g : Nat) (bt : BitVec 64) : List (Nat × Value) :=
  [(1062, b32 (g % L.block / 32)), (2535, b32 L.sharedBase), (7249, Mma.w32 bt)]

def loopOutput (L : Launch) (g : Nat) (bt : BitVec 64) : Nat → Value
  | 631 => .pred (stg L g)
  | 632 => .pred (scmpi .ne .b (Epilogue.andi (tidW L g) 31) 0)
  | 3964 => sbSi L g 80
  | 3970 => .bits 32 (tmS L g)
  | 3971 => .bits 32 (Mma.ori (tmS L g) 96)
  | 3972 => .bits 32 (Mma.ori (tmS L g) 32)
  | 3973 => .bits 32 (Mma.ori (tmS L g) 64)
  | 3976 => .bits 32 (rowSb L g)
  | 3977 => .bits 32 (bOff L g)
  | 4037 => .bits 32 (sbS L g)
  | 7249 => Mma.w32 (addi bt (-1))
  | r => .bits 32 (bAddr L g (bOffs.getD ((r - 3982) / 4) 0))

def loopMid (L : Launch) (g : Nat) (bt : BitVec 64) : Nat → Value
  | 2535 => b32 L.sharedBase
  | 3967 => .bits 32 (tidW L g)
  | 3978 => .bits 32 (Epilogue.add32 (rowSb L g) (bOff L g))
  | 7249 => Mma.w32 bt
  | r => loopOutput L g bt r

def loopKeys (n : Nat) : List Nat :=
  [631, 2535, 3967, 3970, 3971, 3972, 3973, 3976, 3977, 3978, 7249] ++
    (List.range n).map fun i => 3982 + 4 * i

def loopLive (pc : Nat) : List Nat :=
  if pc = 5046 then loopKeys 0
  else (ctlLive pc).filter fun r =>
    loopInputs.contains r || r == 1050 || r == 631 || r == 632 ||
      (decide (3964 ≤ r) && decide (r ≤ 4037))

theorem pwB_loop_start (L : Launch) (g : Nat) (bt : BitVec 64) :
    ∃ n, Seg kernel Assumptions.all L g n 5032 (loopInput L g bt) 5046
      (factsFrom (loopLive 5046) (loopMid L g bt)) := by
  seg_sym using (soft_seg)

theorem pwB_loop_addrs1 (L : Launch) (g : Nat) (bt : BitVec 64) :
    Seg kernel Assumptions.all L g 28 5046 (factsFrom (loopKeys 0) (loopMid L g bt)) 5074
      (factsFrom (loopKeys 7) (loopMid L g bt)) := by
  soft_seg

theorem pwB_loop_addrs2 (L : Launch) (g : Nat) (bt : BitVec 64) :
    Seg kernel Assumptions.all L g 28 5074 (factsFrom (loopKeys 7) (loopMid L g bt)) 5102
      (factsFrom (loopKeys 14) (loopMid L g bt)) := by
  soft_seg


end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
