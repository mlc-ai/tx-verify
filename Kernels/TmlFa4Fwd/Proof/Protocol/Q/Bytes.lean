-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Full
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Input

@[expose] public section

/-! # Every tensor copy moves 16384 bytes -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- **The byte count of the kernel's tensor copies.** -/
theorem tmaBytes {p : Params} {L : Launch} {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X) : TmaBytes X :=
  fun _ _ _ _ he => input_bytes hp hX hFw he

end PTX.Kernels.TmlFa4Fwd.Proof
