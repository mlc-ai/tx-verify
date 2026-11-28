-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiRcp
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
import Kernels.InklingRelDecode.Proof.Common.Export.EpiWait

@[expose] public section

/-! # The epilogue's wait carries its flag and the zero word -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX

/-- **The state after the poll** carries the predicate 173 (no block) and the zero word. -/
theorem epi_wait_of {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    EpiWait L X g (decide (Lib.blocksOf Q L (g / L.block) = 0)) :=
  fun _ hc hpc => Export.epi_wait hp hX hf hc hpc

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
