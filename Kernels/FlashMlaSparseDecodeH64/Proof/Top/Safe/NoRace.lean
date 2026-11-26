-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.AllocRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqOrdered
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Global
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PExchangeAll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Raw
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.RowMax
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.TmaCoord
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.TokenValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Store

@[expose] public section

/-! # ERR-DATA-RACE: conflicting accesses are ordered

The safety class of Core's `Unsafe` this file owns (`Race`), by the reduction of
`Protocol/Shared/Ordered.lean`: memory is ordered once each region of the workspace but the
mbarriers' (which no access covers) is (`RegionOrdered`) and the bytes outside shared memory are
(`global_ordered`). Every region is proved: the dequantized tiles by `dequant_ordered` (with the
output rows `Prog.outRows`), the allocation word by the startup's facts on it
(`tmemWord_ordered_of`, `allocWordRows`), the TMA coordinates and the token-validity bytes by the
index ring (`tmaCoord_ordered`, `tokenValid_ordered`, with the shared inputs' rows), the raw tiles
by the raw ring (`raw_ordered`, without undefined behaviour), the row maxima by warpgroup 0's
barrier 9 (`rowMax_ordered`), the P exchange by its barriers and the score ring
(`pExchange_ordered`). The same facts give ERR-MIXED-SIZE (`Top/Safe/NoMixed.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The regions but the mbarriers' are ordered. -/
theorem Safe.NoRace.regions (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ∀ r, r ≠ .mbars → RegionOrdered L X r
  | .dequant b, _ => dequant_ordered hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
      (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw) (hIn.bar hp X hX hFw)
      (Prog.outRows hp hX hFw hnu) b
  | .raw b, _ => raw_ordered hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
      (hIn.bar0 hp X hX hFw) (hIn.raw hp X hX hFw) hnu b
  | .pExchange, _ => pExchange_ordered hp hX hFw (hIn.bar hp X hX hFw)
      (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw)
  | .rowMax, _ => rowMax_ordered hp hX hFw (hIn.bar hp X hX hFw)
  | .tokenValid, _ => tokenValid_ordered hp hX hFw (hIn.mbar hp X hX hFw)
      (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.coord hp X hX hFw)
  | .tmaCoord, _ => tmaCoord_ordered hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
      (hIn.bar0 hp X hX hFw) (hIn.coord hp X hX hFw)
  | .tmemWord, _ => tmemWord_ordered_of hp hX hFw (allocWordRows hp hX hFw)
  | .mbars, h => (h rfl).elim

/-- **ERR-DATA-RACE**: conflicting accesses are ordered. -/
theorem Safe.noRace (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ Race L X :=
  no_race hp hX hFw (Safe.NoRace.regions hp hIn hX hFw hnu) (global_ordered hp hX hFw hnu)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
