-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueAllocationTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Lemmas.Clc.ClcExecution
import Lemmas.Flow.OpPcsFast

public section

/-! # The prefix of a complete allocating warp before its address read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
open PTX PTX.Flow

/-- The allocating warp's prologue up through the instruction's own address write. -/
@[expose] def beforeRead : Site → Bool
  | .shfl0 | .shfl1 | .elect0 | .elect1 | .init _ | .fence | .alloc | .allocStore => true
  | _ => false

private def isExitOp : Op → Bool
  | .ret | .exit => true
  | _ => false

private def Prefix (P : Params) (L : Launch) (g : Nat) (es : List Event) : Prop :=
  ∀ k < es.length, ∃ s, beforeRead s = true ∧
    (Machine.machine P L g).after (Machine.machine P L g).init (es.take k) =
      some (some (.prologue s))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
