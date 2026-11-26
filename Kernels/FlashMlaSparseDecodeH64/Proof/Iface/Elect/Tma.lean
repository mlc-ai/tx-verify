-- SPDX-License-Identifier: Apache-2.0
-- iface: TmaOne producer=A status=row-proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma

@[expose] public section

/-! # One TMA lane per CTA (election fact, producer A)

Warp 5 elects at pc 2165 (`code_elect_7`, full mask); the losers walk to the idle code (pcs
2587 on), so only the winner has events at the TMA pcs after the election (`TmaOn`: `TmaAt` and
`2165 < pc`). `TmaOne` says two lanes of one CTA with such events are one lane.

**Proved** by lane A: `tmaOne` (`Tma/Export/Elect.lean`). An event (not undefined behaviour) of
lane `g` at a `TmaOn` pc follows `g`'s election at pc 2165 with the full mask whose leader is
`g`'s own lane (`tma_won`, `Common/TmaWon.lean`: a loser is handed back to the idle code and the
thread machine never leaves it); two such lanes of warp 5 of one CTA are one lane by
`elect_winner` (`Lemmas/Kernel/ElectSource.lean`). Not a classification row (not `ahead`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- Lane `g` at `pc` is in the TMA code after the election. -/
def TmaOn (L : Launch) (g pc : Nat) : Prop := MbarRow.TmaAt L g pc ∧ 2165 < pc

/-- **One TMA lane per CTA**: two lanes of one CTA with events at TMA pcs after the election
are one lane. -/
def TmaOne (L : Launch) (X : Execution) : Prop := OneLane L X (TmaOn L)

/-- The TMA lane of CTA `c`. -/
abbrev tmaLane (L : Launch) (X : Execution) (c : Nat) : Nat := laneOn L X (TmaOn L) c

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
