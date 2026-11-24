-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompMachine
public import Kernels.InklingRelDecode.Proof.Thread.SmDischarge
public import Kernels.InklingRelDecode.Proof.Thread.DCompFollows

/-! # The Inkling default-partition thread (warps 0 to 3) as one site machine: umbrella

`DCompBase` (the composed states, facts, invariant, successors and `code`), `DCompTail` (the
softmax region's obligations `SmObligations` and its `Code.StepAt` at every site), `DCompNext`
(what the prologue's successors preserve, the bridge's dead states) and `DCompMachine` (`stepAt`,
`sound`, `machine_sound`) and `SmDischarge` (`SmObligations` from `ScoreRest`, the one premise about
the launch that the thread proof leaves). -/
