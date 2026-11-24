-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Flow.Polls
public import Lemmas.Kernel.Safety.Classes

/-! # What a role's export is stated with

The execution, the launch, the following premise, the warp index, the CTA's objects and the trace's
prefix counts: the imports of every `<Role>/Export/Mbar` and `Count`. -/
