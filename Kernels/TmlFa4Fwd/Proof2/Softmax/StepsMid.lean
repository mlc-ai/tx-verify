-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsMid0
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBld1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBld2

@[expose] public section

/-! # The softmax warps' sub-steps that stay at their instruction

The elements of a bias load before the last (sub-steps 0 to 2: the read value is accumulated),
the implicit wait of a round's first P store (sub-step 0 of a `delayedTmem` site) and a plain
round's score load (sub-step 0 of a `tcLdDataflow` site): one file per family
(`StepsMid0.lean`, `StepsBld1.lean`, `StepsBld2.lean`). None of them runs local code. -/
