-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsBBase
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocol

@[expose] public section

/-!
# The share of the Compute phase for the rings and the state copy

`FactsBBase.lean` proves four contracts of the protocol layer from `FactsB.ComputeOwes`: seven
facts about the events of a compute thread in its tile loop (the Compute phase, instructions
2106 to 2944), each about an event or a memory access at a followed state with the phase's
invariant. This file proves the structure for every consistent execution, from the export file
of the Compute phase for the protocol layer (`Ref/Compute/ExportsProtocol.lean`, namespace
`Compute.Proto`), which states one theorem per field:

| field | theorem of `Compute.Proto` | what it rests on |
|---|---|---|
| `kinds` | `owes_kinds` | the closed-form event of every position of a tile |
| `poll` | `owes_poll` | the two polls of a tile and the phase's count of successful polls |
| `arrive` | `owes_arrive` | the two arrivals of a tile and the counts of polls and arrivals |
| `in_fence` | `owes_in_fence` | the proxy fence is two events before the second arrival |
| `out_fence` | `owes_out_fence` | the proxy fence is the event before the first arrival |
| `acc_phase` | `owes_acc_phase` | every access is in the thread's own block, in a tile |
| `acc_owner` | `owes_acc_owner` | the rows of the state copy of two threads share no byte |

A *position* of a tile is the index (0 to 267) of an event in the straight line of the 268
events of the tile: 0 and 1 the two polls, 264 the named barrier, 265 the proxy fence, 266 and
267 the two arrivals, the others the events of the matrix instructions and scalar loads.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsB
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The share of the Compute phase holds for every consistent execution.** -/
theorem computeOwes (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    ComputeOwes P L X where
  kinds := Compute.Proto.owes_kinds hpre hX
  poll := Compute.Proto.owes_poll hpre hX
  arrive := Compute.Proto.owes_arrive hpre hX
  in_fence := Compute.Proto.owes_in_fence hpre hX
  out_fence := Compute.Proto.owes_out_fence hpre hX
  acc_phase := Compute.Proto.owes_acc_phase hpre hX
  acc_owner := Compute.Proto.owes_acc_owner hpre hX

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsB
