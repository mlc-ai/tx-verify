-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Flow.Code
import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # The softmax warps' sub-steps that stay at their instruction

The elements of a bias load before the last (sub-steps 0 to 2: the read value is accumulated),
the implicit wait of a round's first P store (sub-step 0 of a `delayedTmem` site) and a plain
round's score load (sub-step 0 of a `tcLdDataflow` site): one file per family
(`StepsMid0.lean`, `StepsBld1.lean`, `StepsBld2.lean`). None of them runs local code. -/
