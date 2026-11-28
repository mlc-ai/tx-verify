-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.StaticCode

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noTcCommit (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) :
    ¬ TcCommitUnsafe L X :=
  Lib.noTcCommitUnsafe hp hX

end PTX.Kernels.InklingRelDecode.Proof.Top
