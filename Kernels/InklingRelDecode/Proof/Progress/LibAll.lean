-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.LibReg
public import Kernels.InklingRelDecode.Proof.Progress.LibTmem
public import Kernels.InklingRelDecode.Proof.Progress.LibBar

@[expose] public section

/-!
# The library gaps of the progress layer (umbrella)

Kernel-local generic lemmas for the three gaps of `Remaining` (`regIssue`, `barSteps`,
`tmemSteps`), each marked in its doc comment for promotion to `Lemmas/`.
-/
