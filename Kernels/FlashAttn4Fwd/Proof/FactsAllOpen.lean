-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.SafeFacts
public import Kernels.FlashAttn4Fwd.Proof.ResultFacts
public import Kernels.FlashAttn4Fwd.Proof.Progress.Assembly
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMachine
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWaits
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccessRoles
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsBar2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarpRoles
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollSched
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarpColl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedTc

@[expose] public section

/-! # The thread facts not yet proved: none

This file bundled, as `Open`, the statements the assembly of the thread layer's interface
(`FactsAll*.lean`) still took as premises. Every one is now proved, so it holds nothing; it keeps
the imports the assembly files share. -/
