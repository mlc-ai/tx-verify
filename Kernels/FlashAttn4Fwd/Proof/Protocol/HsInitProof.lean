-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAllocHandshake

@[expose] public section

/-! # The handshake barrier's initialization premise

`HsInit` (`TmemAlloc.HsInit`) is the handshake barrier's initialization being its first record,
without fault, and its only one, with count 32. It is `InitFirst.deallocInit`: the initialization
is published to every other record's issuer by the start cluster barrier
(OBJ-MBAR-INIT-PUBLICATION). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.HsInitProof
open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The handshake barrier's initialization premise holds.** -/
theorem hsInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hc : ClusterFacts L X) (htm : TmemFacts L X) (hi : InitFacts L X) (cta : Nat) :
    TmemAlloc.HsInit L X cta :=
  InitFirst.deallocInit hpre hX hc htm hi cta

end
end PTX.Kernels.FlashAttn4Fwd.Proof.HsInitProof
