-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Assumptions

/-- The first P stores in the initial and repeated biased rounds. -/
def delayedTmemSites : List Nat := [4826, 6508]

/-- The score loads of one biased round have completed by its first P store. -/
def delayedTmem : Assumption where
  name := "tml-fa4-fwd-consumed-bias-score-reads"
  statement := "The score loads at pcs 3428, 3446, 3463 and 3481 have completed before the first \
    P store at pc 4826, and the score loads at pcs 5112, 5129, 5146 and 5163 have completed before \
    the first P store at pc 6508. In each round all 32 destinations of each score load have \
    already been consumed by the score FMAs. The model treats those reads as complete at the \
    first P store, including for cross-warp reuse and allocation release."
  tcStWaitLd pc := delayedTmemSites.contains pc

end PTX.Kernels.TmlFa4Fwd.Assumptions
