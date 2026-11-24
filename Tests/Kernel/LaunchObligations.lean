-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Spec

/-! # Launch obligations checked on the kernels' data (EXT-LAUNCH)

The Tensor Memory obligation of EXT-LAUNCH asks that the total number of columns that the
CTAs co-resident on one SM, of this or of any other kernel, may request through
`tcgen05.alloc` at once never exceeds what one SM provides. The production GEMM
needs 230400 bytes of shared memory per CTA, more than half of the 233472 bytes (228 KiB)
an sm_100 SM provides (CUDA C++ Programming Guide, compute capability 10.0: maximum shared
memory per SM 228 KB), so at most one of its CTAs is resident per SM; that no co-resident CTA
of another kernel allocates Tensor Memory is an obligation of the launch. -/

namespace PTX.Tests.LaunchObligations

example : 233472 < 2 * PTX.Kernels.Fp16Gemm8192.sharedBytes := by decide

end PTX.Tests.LaunchObligations
