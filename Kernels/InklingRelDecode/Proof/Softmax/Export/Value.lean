-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Start
import Kernels.InklingRelDecode.Proof.Softmax.GenRules
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Seq

@[expose] public section

/-! # The softmax's value machine, for the glue above the roles

`Common/ValueThread.lean` takes the softmax slot's machine from here: `Data.codeS`, its erasure
`Data.D.c` to the control machine, `Data.erasesS`, and the steps of every state `Data.stepAtS`. -/
