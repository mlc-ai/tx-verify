-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Protocol.MbarRingRound
public import Lemmas.Order.DependencyWitness

@[expose] public section

/-! # Slot reuse and counter-update witnesses for the index and raw KV rings -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol

open PTX AsyncCopy MBarrier

/-- A block's slot in the four-slot index ring. -/
def indexSlot (block : Nat) : Fin 4 := ⟨block % 4, Nat.mod_lt _ (by decide)⟩

/-- A block's slot in the two-buffer raw KV ring. -/
def rawSlot (block : Nat) : Fin 2 := ⟨block % 2, Nat.mod_lt _ (by decide)⟩

/-- The named object's address in one CTA's shared window. -/
def Mbar.loc (m : Mbar) (L : Launch) (cta : Nat) : Loc :=
  ⟨.shared, cta, L.sharedBase + m.off⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol
