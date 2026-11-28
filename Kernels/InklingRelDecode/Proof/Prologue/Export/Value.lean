-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Step

@[expose] public section

/-! # The prologue's value machine, for the glue above the roles

`Common/ValueThread.lean` takes the prologue slot's machine from here: `Data.code`, its erasure
`Data.D.c` to the control machine and `Data.erases`, and the data step of every state
`Data.data_step`. -/
