-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSw

@[expose] public section

/-! # A loop tile's row maximum: the common imports

The values at the checkpoints of a loop tile's row maximum are those of the read run
(`exMax1_2926`, `SoftmaxReads`) and of the outcome run `max1T` (`SoftmaxRuns`). -/
