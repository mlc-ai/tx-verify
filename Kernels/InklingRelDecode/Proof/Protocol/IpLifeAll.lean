-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeFinal

/-!
# The shared lifetime: umbrella

`IpLifeUse` (the table of shared uses and the assembly), `IpLifeOwn` (placement), `IpLifeExit` (a
default-partition thread exits after a poll of `o_final`), `IpLifeMma`, `IpLifeCopy`,
`IpLifeCommit` (the finishing facts), `IpLifeFinal` (`Life.lifetime`).
-/
