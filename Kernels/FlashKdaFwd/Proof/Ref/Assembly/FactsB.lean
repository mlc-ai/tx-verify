-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsBOwes
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsA

@[expose] public section

/-!
# Assembly, group B: the rings and the state copy

Four of the seven contracts of the protocol layer (`Proof/Protocol/Export.lean: Facts`), for
every consistent execution of the kernel under the precondition:

    theorem loadFacts     (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
        Protocol.LoadFacts L X
    theorem storeFacts    (hpre) (hX) : Protocol.StoreFacts L X
    theorem stateFacts    (hpre) (hX) : Protocol.StateFacts L X
    theorem stateAccFacts (hpre) (hX) : Protocol.StateAccFacts L X

and the seven together, with the three theorems of `FactsA.lean` (`barFacts`, `initFacts`,
`lifeFacts`: barrier events, mbarrier initialization, exits):

    theorem facts (hpre) (hX) : Protocol.Facts P L X

No other hypothesis remains.

The proofs are in `FactsBBase.lean` (one classification per kind of event (arrival on an
mbarrier, poll, tensor load, tensor store, memory access) by the case principle of `Stage.lean`,
each field from the classification of its event, and one structure of facts about the Compute
phase, `FactsB.ComputeOwes`) and `FactsBOwes.lean` (that structure, from the export file of the
Compute phase). Everything but the five theorems below is in the namespace `Assembly.FactsB`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The contract of the load pipeline** (three stages; per stage a "full" mbarrier fed by the
load leader's arrival and 70 tensor loads, and an "empty" mbarrier fed by the 128 compute
threads) for every consistent execution. -/
theorem loadFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    LoadFacts L X :=
  FactsB.loadFacts_of hpre hX (FactsB.computeOwes hpre hX)

/-- **The contract of the store pipeline** (two stages; per stage a "full" mbarrier fed by the
128 compute threads and an "empty" mbarrier fed by the store leader) for every consistent
execution. -/
theorem storeFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    StoreFacts L X :=
  FactsB.storeFacts_of hpre hX (FactsB.computeOwes hpre hX)

/-- **The contract of the state mbarrier** (the one-shot barrier of the sixteen tensor loads of
the initial state) for every consistent execution. -/
theorem stateFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    StateFacts L X :=
  FactsB.stateFacts_of hpre hX (FactsB.computeOwes hpre hX)

/-- **The contract on the accesses of the bfloat16 state copy `state_acc`** (only threads
touch it; in the conversion loop and in the tile loop; each byte by one thread per phase) for
every consistent execution. -/
theorem stateAccFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    StateAccFacts L X :=
  FactsB.stateAccFacts_of hpre hX (FactsB.computeOwes hpre hX)

/-- **The contract of the exports layer** (`Protocol.Facts`: the seven structures of thread
facts of the protocol layer) for every consistent execution: the three structures of group A
(`FactsA.lean`) and the four above. -/
theorem facts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    Facts P L X :=
  FactsB.facts_of hpre hX (FactsB.computeOwes hpre hX) (barFacts hpre hX) (initFacts hpre hX)
    (lifeFacts hpre hX)

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
