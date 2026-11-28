-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollKey
public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # The warp collectives of the code

Every shuffle, election and warp barrier of the decoded program is at one of the pcs of `collPcs`
and has an immediate static part or is an election. (The ballot count is `kernel_noBallot`; the mode
vote at pc 578 is no collective of the count.) -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

/-- An instruction that fires a warp collective of the count. -/
def collOp : Op → Bool
  | .warp w => match w.kind with
    | .shfl _ | .elect | .barWarp | .vote .ballot _ => true
    | _ => false
  | _ => false

/-- The pcs of the code's warp collectives: shuffles (startup 6, 9; warp 6's head 1843; the index
warp's 2464, 2467, 2553, 2556) and elections (startup 16, 31; warpgroup 0's epilogue 1350, 1507,
1664, 1822; the MMA warp's 1853; the TMA warp's 2165). -/
def collPcs : List Nat :=
  [6, 9, 16, 31, 1350, 1507, 1664, 1822, 1843, 1853, 2165, 2464, 2467, 2553, 2556]

/-- Decidable form of `CollIns`. -/
def collInsB (ins : Instr) : Bool := (opShape ins.op).isSome || electOp ins.op

/-- The static part of the instruction at a pc: its immediate shuffle operands, or the full-mask
election's. -/
def pcShape (pc : Nat) : Sched.CollShape :=
  ((kernel.code[pc]?).bind fun ins => opShape ins.op).getD (.elect 4294967295)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
