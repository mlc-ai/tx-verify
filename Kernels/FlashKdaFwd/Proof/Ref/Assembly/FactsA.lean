-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsAOwes

@[expose] public section

/-!
# Assembly, group A: barriers, mbarrier initialization, lifetimes

Three of the seven contracts of the protocol layer (`Proof/Protocol/Export.lean: Facts`), for
every consistent execution of the kernel under the precondition:

    theorem barFacts  (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
        Protocol.BarFacts L X (ctaTiles P)
    theorem initFacts (hpre) (hX) : Protocol.InitFacts L X
    theorem lifeFacts (hpre) (hX) : Protocol.LifeFacts L X (ctaTiles P)

No other hypothesis remains. `ctaTiles P c` is the number of 16-token tiles of thread block
`c`.

The proofs are in `FactsABase.lean` (the sixteen fields, from the case principle of
`Stage.lean` and two structures of facts about the Compute phase and the Store phase) and
`FactsAOwes.lean` (the two structures, from the export files of the two phases). Everything but
the three theorems below is in the namespace `Assembly.FactsA`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The barrier contract** (`bar.sync 0` and the named barrier `bar.sync 8, 128`) for every
consistent execution. -/
theorem barFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    BarFacts L X (ctaTiles P) :=
  FactsA.barFacts_of hpre hX (FactsA.computeOwes hpre hX)

/-- **The contract on the initialization and the use of the eleven mbarriers** for every
consistent execution. -/
theorem initFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    InitFacts L X :=
  FactsA.initFacts_of hpre hX (FactsA.computeOwes hpre hX) (FactsA.storeOwes hpre hX)

/-- **The lifetime contract** (asynchronous uses of shared memory end before the block exits)
for every consistent execution. -/
theorem lifeFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    LifeFacts L X (ctaTiles P) :=
  FactsA.lifeFacts_of hpre hX (FactsA.storeOwes hpre hX)

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
