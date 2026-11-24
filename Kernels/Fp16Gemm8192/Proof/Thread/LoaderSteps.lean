-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.step_load
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.trip_end
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.step_lastLoad
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.step_arrive

@[expose] public section

/-! # The loader's K loop: loads and arrivals

After a tensor load or a full-slot arrival the loader continues at the next instruction.
Within a block the next event is the next load. After the last load the code branches on
the CTA's rank in its cluster: the leader arrives on the full barrier, the other CTA goes
to the next block. After the last block the code branches on whether the trip was the last
one. Both branches are evaluated by splitting the segment at the branch (`run_bra`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000



end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
