-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.ReadValue
public import Lemmas.Step.WarpVote
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.WarpScan
public import Lemmas.Step.WarpShfl
public import Lemmas.Flow.TauFrame
public import Kernels.TmlFa4Fwd.Proof.CuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.PrologueScheduler
public import Kernels.TmlFa4Fwd.Proof.WarpFollows
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof Prologue

noncomputable section

variable {A : List Assumption}

/-- The first scheduler shuffle uses an immutable cumulative Q word, or zero beyond the sentinel. -/
def firstSchedulerWord (p : Params) (lane : Nat) : Nat :=
  if p.batch < lane then 0 else p.qOffset lane

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
