-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoUnalloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoRace
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoMixed
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoAligned
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoSharedLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTensor
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemAccess
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemInstruction
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoRegister
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemRest
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoClc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoAssumptionUb
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTensorAllocation
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTensorStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoPollShape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTcCommit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoClusterFault
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoWarpDivergence
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoMatrix
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoUninit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoBarMismatch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoCtaBar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemRelease

@[expose] public section

/-! # Safety by class

`SafeGoal` for every consistent execution, split by the classes of Core's `Unsafe`, one file per
class (`Top/Safe/<Class>.lean`). A class that is a static check of the decoded program is proved
in its file from `Lib/StaticCode.lean`, `Lib/StaticPoll.lean` or `Lib/StaticCommit.lean` (no
cancellation, tensor-store reduction, poll shape, commit group, cluster barrier, warp divergence
or warp matrix fault); the uniform Tensor Core group is `kernel_groupUniform`. A class proved
from the shared inputs (`Top/Inputs.lean`) is called as `Safe.<class> hp hIn hX hFw` with
`hIn := Inputs.of_pre hp` (the
initialization of the mbarriers, `Safe.noUninit`; their lifetimes, `Safe.noTma`; the warps'
barriers, `Safe.noBarMismatch`, `Safe.noCtaBar`; the Tensor Memory allocator,
`Safe.noTmemResource`, `Safe.noTmemRelease`; the Tensor Memory writes and MMA reads,
`Safe.noTmemWrites`, `Safe.noTmemReads`). Every other class is called as
`Safe.<class> hp hX hFw`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Safety**: no consistent execution is unsafe, class by class. -/
theorem safe (hp : Pre P L mem0) :
    SafeGoal kernel Assumptions.all L mem0 := by
  refine ⟨kernel_groupUniform, fun X hX hBad => ?_⟩
  have hFw := follow_of hp X hX
  have hIn := Inputs.of_pre hp
  simp only [Unsafe, Safe.noUb hp hX hFw,
    Safe.noUnalloc hp hIn hX hFw (Safe.noUb hp hX hFw),
    Safe.noRace hp hIn hX hFw (Safe.noUb hp hX hFw),
    Safe.noMixed hp hIn hX hFw (Safe.noUb hp hX hFw),
    Safe.noBarMismatch hp hIn hX hFw, Safe.noTma hp hIn hX hFw,
    Safe.noTmemSource hp hIn (Safe.w0TraceValid hp) hX hFw (Safe.noUb hp hX hFw),
    Safe.noAssumptionUb hp hX hFw (Safe.noUb hp hX hFw),
    Safe.noAligned hp hIn hX hFw (Safe.noUb hp hX hFw),
    Safe.noSharedLifetime hp hIn hX hFw
      (Safe.noUb hp hX hFw),
    Safe.noClc hp hX, Safe.noTensor hp hX hFw, Safe.noTensorStore hp hX,
    Safe.noTensorAllocation hp hX hFw (Safe.noUb hp hX hFw),
    Safe.noTmemResource hp hIn hX hFw, Safe.noTmemRelease hp hIn hX hFw,
    Safe.noPollShape hp hX, Safe.noTmemAccess hp hIn hX hFw,
    Safe.noTcCommit hp hX,
    Safe.noTmemWrites hp hIn hX hFw,
    Safe.noTmemInstruction hp (Safe.completed hp hIn (Safe.w0TraceValid hp) hX hFw
      (Safe.noUb hp hX hFw)) hX hFw,
    Safe.noTmemReads hp hIn hX hFw,
    Safe.noRegister hp hX hFw (Safe.noUb hp hX hFw),
    Safe.noCtaBar hp hIn hX hFw, Safe.noClusterFault hp hX, Safe.noWarpDivergence hp hX,
    Safe.noMatrix hp hX, Safe.noUninit hp hIn hX hFw, or_self] at hBad

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
