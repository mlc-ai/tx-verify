-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileHyps
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileOut
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileNoUb
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.TileEnds
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ValuesEnds
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsB
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Buffers
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct

@[expose] public section

/-!
# The value side, collected for its two consumers

The value layers prove what the DATA of the kernel are: the tile value induction
(`Proof/Values/`) for the tile loop of the compute threads, and the value ends
(`Proof/Values/Ends/`) for the four stretches around it (the conversion loop, the carry loads,
the final stores, the store path of a partial last tile). Two structures of the layers above
consume the results:

* `Protocol.OutContent P L X O` (`Proof/Protocol/ResultGlue.lean`): what the compute threads
  wrote into the buffers that the store leader copies out. It is the value layer's share of
  the result facts (`Protocol.resultFacts_of_contracts`).
* `DataHalf P L mem0 X` (`DirectData.lean`): the data half of "no undefined-behaviour event"
  (per family of sites at which the outcome of an event depends on a data value) and the
  operands of the warp-level multiply-accumulates. It is what the assembly of the direct
  facts takes from the value side (`Direct.lean: direct`).

This file builds both, for every consistent execution under the launch precondition, from the
final theorems of the files that proved the fields:

| structure | field | from |
|---|---|---|
| `OutContent` | `stage` | `outContent_stage` (`TileOut.lean`), from the claim of the induction |
| | `elem` | `out_elem'` (`ValuesEnds.lean`) |
| | `final` | `out_final'` (`ValuesEnds.lean`), from the carries after the last tile |
| `DataHalf` | `convLoad`, `convStore`, `carryLoad` | `dataHalf_…` (`ValuesEnds.lean`) |
| | `matrixEv`, `tileNext` | `TileNoUb.lean`, from the claim of the induction |
| | `elemRead`, `elemStore` | `dataHalf_…` (`ValuesEnds.lean`), with `stage` above |
| | `finalStore` | `dataHalf_finalStore` (`ValuesEnds.lean`) |
| | `mmaOperands` | `mmaOperands` (`TileOutMma.lean`), from the claim of the induction |

**Words.** The *claim* is `Values.TileClaim P L mem0 X`, the conclusion of the induction over
the tiles (`Proof/Values/TileClaim.lean`); the *induction* is the theorem
`Values.tile_induction` (`Proof/Values/Tile.lean`: the hypotheses record `Values.TileHyps`
gives the claim). `Values.Ends.FinalCarries P L X` says that at the first final store the carry
registers of a compute thread hold the state after the last token of its sequence. `O : Owners`
are the four functions of the protocol layer that name the writer of a byte of the buffer
region; `owners P L` are the ones for which the classification of the buffer region is proved
(`Buffers.lean`).

**What is supplied here.** The hypotheses record of the induction (`TileHyps.lean: tileHyps`)
is completed with

* the protocol contracts `facts`, `unionFacts`, `storeCover` (`FactsB.lean`, `Buffers.lean`);
* the two facts about the sources of the tensor loads that the read-backs need:
  `TileHyps.stateIssues` (`TileHyps.lean`) and `Direct.writeFrame` (`Direct.lean`: every
  global write is to an output array);
* the read-back of the bfloat16 state copy `readBack_acc` (`ValuesEnds.lean`);
* the base case `tileBase` (`TileEnds.lean`), with the contracts of the carry loads `carryRef`
  and `ValuesEnds.earlyRead` (`ValuesEndsRef.lean`).

No hypothesis remains on `outContent` and `dataHalf` besides the precondition and consistency.

Helpers are in the namespace `Assembly.Values`; the final theorems `outContent` and `dataHalf`
are in `Assembly`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (Facts UnionFacts StoreCover Owners ctaTiles OutContent)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Values

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-! ### From the claim and the carries after the last tile -/

/-- **`OutContent` from the claim and the carries after the last tile**, for any owner
functions `O` (none of the three fields uses what `O` names). -/
theorem outContent_of (T : Values.TileClaim P L mem0 X)
    (hfin : Values.Ends.FinalCarries P L X) (O : Owners) : OutContent P L X O where
  stage := outContent_stage hpre hX T O
  elem := fun hs hh ht hk hw hc hread => out_elem' hpre hX hs hh ht hk hw hc hread
  final := fun hs hh hb hst hwl hrl ga iw aw bw hown hlast =>
    out_final' hpre hX hfin hs hh hb hst hwl hrl ga iw aw bw hown hlast

/-- **`DataHalf` from the claim and the carries after the last tile**, given the protocol
contracts for some owner functions `O` and the two facts about the sources of the loads. -/
theorem dataHalf_of (T : Values.TileClaim P L mem0 X)
    (hfin : Values.Ends.FinalCarries P L X) {O : Owners} (F : Facts P L X)
    (U : UnionFacts L X (ctaTiles P) O) (C : StoreCover L X O)
    (hSI : Source.StateIssues P L X) (hW : Source.WriteFrame P X) : DataHalf P L mem0 X :=
  have hrd : Values.Ends.LeaderReads P L X :=
    ValuesEnds.leaderReads hpre hX F U C
      (ValuesEnds.OutStage.of (outContent_of hpre hX T hfin O))
  { convLoad := dataHalf_convLoad hpre hX F U hSI hW
    convStore := dataHalf_convStore hpre hX F U hSI hW
    carryLoad := dataHalf_carryLoad hpre hX F U hSI hW
    matrixEv := matrixEv hpre hX T
    tileNext := tileNext hpre hX T
    elemRead := dataHalf_elemRead hpre hX hrd
    elemStore := dataHalf_elemStore hpre hX hrd
    finalStore := dataHalf_finalStore hpre hX hfin
    mmaOperands := mmaOperands hpre hX T }

/-! ### The induction, with its hypotheses supplied -/

/-- **What a read of the FP32 state buffer returns before the tile loop**
(`Values.Ends.EarlyRead`), with the protocol contracts and the sources' facts supplied. -/
theorem early : Values.Ends.EarlyRead P L X :=
  ValuesEnds.earlyRead hpre hX (facts hpre hX) (unionFacts hpre hX)
    (TileHyps.stateIssues hpre hX) (Direct.writeFrame hpre hX)

/-- **The hypotheses record of the induction over the tiles** (`Values.TileHyps`). -/
theorem hyps : Values.TileHyps P L mem0 X :=
  tileHyps hpre hX (facts hpre hX) (unionFacts hpre hX) (Direct.writeFrame hpre hX)
    (readBack_acc hpre hX (facts hpre hX) (unionFacts hpre hX) (storeCover hpre hX)
      (TileHyps.stateIssues hpre hX) (Direct.writeFrame hpre hX))
    (tileBase hpre hX (carryRef hpre hX) (early hpre hX))

/-- **The claim of the induction over the tiles**, for a consistent execution under the launch
precondition. -/
theorem claim : Values.TileClaim P L mem0 X :=
  Values.tile_induction (hyps hpre hX)

/-- **The carries after the last tile** (`Values.Ends.FinalCarries`), from the claim. -/
theorem carries : Values.Ends.FinalCarries P L X :=
  finalCarries hpre hX (carryRef hpre hX) (early hpre hX) (claim hpre hX)

end

end Values

/-! ### The two structures -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **The content of the compute threads' writes** (`Protocol.OutContent`, the value layer's
share of the result facts), for any owner functions `O`, in particular for `owners P L`. -/
theorem outContent (O : Owners) : OutContent P L X O :=
  Values.outContent_of hpre hX (Values.claim hpre hX) (Values.carries hpre hX) O

/-- **The data half of "no undefined-behaviour event" and the operands of the
multiply-accumulates** (`DataHalf`, `DirectData.lean`). -/
theorem dataHalf : DataHalf P L mem0 X :=
  Values.dataHalf_of hpre hX (Values.claim hpre hX) (Values.carries hpre hX)
    (facts hpre hX) (unionFacts hpre hX) (storeCover hpre hX) (TileHyps.stateIssues hpre hX)
    (Direct.writeFrame hpre hX)

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
