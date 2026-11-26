-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemInstruction
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemResource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.TmEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order

@[expose] public section

/-! # The values of the completed MMAs

Every completed MMA's unmasked result is defined (`TcMma.CompletedValues`): by induction along the
the tcgen05 order (`TmRace.completed_values`), from the finiteness of the operand elements and
the validity of warpgroup 0's trace, which makes its rescale stores' words numbers
(`Safe.W0TraceValid`). The class's other checks and the sources of
the reads are proved in `NoTmemInstruction.lean` and `NoTmemSource.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Every completed MMA has its result**: the unmasked cells of a done MMA have a value. -/
theorem Safe.completed (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      TcMma.CompletedValues L Assumptions.all X i := by
  intro i d s acc mask hi
  have env := Safe.tmEnv hp hIn hR hX hFw hnu
  exact TmRace.completed_values hp hX hFw (tmem_rows hp hX hFw) (mmaOne hp hX hFw)
    (Safe.pvStore hp hIn hX hFw) (Safe.guarded hp hIn hX hFw) (Safe.tmemOne hp hIn hX hFw) env.hmd
    (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw)
    (hIn.dequant hp X hX hFw) (hIn.bar hp X hX hFw) env.hE env.hS hi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
