-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerStart

/-! # The Inkling workers: umbrella

`Worker` (the machine), `WorkerStep` and `WorkerSound` (its steps and `stepAt`), `WorkerIdle` (the
idle role), `WorkerHandoff` (the loader, the MMA warp, the exit and the return to the loop) and
`WorkerStart` (the code from the launch to the first barrier). -/
