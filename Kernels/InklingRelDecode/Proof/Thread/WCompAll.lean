-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompMachine

/-! # The Inkling worker thread (warps 4 to 7) as one site machine: umbrella

`WCompBase` (the composed states, facts, invariant, successors and `code`), `WCompEntry` (the
entries of the roles, their returns to the dispatch loop and the exit's step), `WCompNext` (what
the successors preserve), `WCompSound` (the steps of the worker, idle and loader states) and
`WCompMachine` (the MMA and exit states, `stepAt`, `sound`, `machine_sound`). -/
