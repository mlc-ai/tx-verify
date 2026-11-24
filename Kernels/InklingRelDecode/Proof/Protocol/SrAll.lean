-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SrAlias
public import Kernels.InklingRelDecode.Proof.Protocol.SrCells
public import Kernels.InklingRelDecode.Proof.Protocol.SrCoord
public import Kernels.InklingRelDecode.Proof.Protocol.SrOrder
public import Kernels.InklingRelDecode.Proof.Protocol.SrReads
public import Kernels.InklingRelDecode.Proof.Protocol.SrWrites

@[expose] public section

/-!
# The Tensor Memory orders of the S/P/O handshake: umbrella

`SrCells` (the cells of the softmax region's `tcgen05.st` stores), `SrOrder` (the orders between
the MMA lane and a softmax store from the handshake's polls), `SrCoord` (the coordinates of the
writers and readers of one CTA: `Lane`), `SrWrites` (`Sr.no_writes_unsafe`:
`Safety.Protocol.tcWrites`), `SrReads` (`Sr.no_reads_unsafe`: `Safety.Protocol.tcReads`),
`SrAlias` (`Sr.pAliasSync_S`: the S load before the `P` store of the other half).
-/
