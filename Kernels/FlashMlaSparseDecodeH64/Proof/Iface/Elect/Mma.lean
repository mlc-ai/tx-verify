-- SPDX-License-Identifier: Apache-2.0
-- iface: MmaOne producer=B status=row-proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma

@[expose] public section

/-! # One MMA lane per CTA (election fact, producer B)

Warp 4 elects at pc 1853 (`code_elect_6`, full mask); the losers walk to the idle code (pcs
2587 on), so only the winner has events at the MMA pcs after the election (`MmaOn`: `MmaAt` and
`1853 < pc`). `MmaOne` says two lanes of one CTA with such events are one lane.

**Proved** by lane B: `mmaOne` (`Mma/Export/Elect.lean`). An event (not undefined behaviour) of
lane `g` at an `MmaOn` pc follows `g`'s election at pc 1853 with the full mask whose leader is
`g`'s own lane (`mma_won`, `Common/MmaWon.lean`: a loser is handed back to the idle code and the
thread machine never leaves it); two such lanes of warp 4 of one CTA are one lane by
`elect_winner` (`Lemmas/Kernel/ElectSource.lean`). Not a classification row (not `ahead`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- Lane `g` at `pc` is in the MMA code after the election. -/
def MmaOn (L : Launch) (g pc : Nat) : Prop := MbarRow.MmaAt L g pc ∧ 1853 < pc

/-- **One MMA lane per CTA**: two lanes of one CTA with events (not undefined behaviour) at MMA
pcs after the election are one lane. -/
def MmaOne (L : Launch) (X : Execution) : Prop := OneLane L X (MmaOn L)

/-- The MMA lane of CTA `c`. -/
abbrev mmaLane (L : Launch) (X : Execution) (c : Nat) : Nat := laneOn L X (MmaOn L) c

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
