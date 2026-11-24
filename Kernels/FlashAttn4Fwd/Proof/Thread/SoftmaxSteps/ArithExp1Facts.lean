-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithSw

@[expose] public section

/-! # The exponentials of a loop tile: the common imports

The values at the checkpoints of the exponentials are the outcome runs' (`exp1Pieces`,
`SoftmaxRuns`), from the table of the state at the named barrier. -/
