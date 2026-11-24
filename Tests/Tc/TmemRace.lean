-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TmemRace

/-! # ERR-TMEM-RACE's write half for one MMA thread and one store thread per cell

The shape of tml-fa4's and FA4's Tensor Memory: one lane issues every MMA, with one accumulator
per region; each cell's stores are one thread's; no copy or shift. The write half of the race
check is then the MMA/store order alone (`writesSafe_of` with `mm_of_po` and `ss_of_po`). -/

namespace PTX.Tests.TmemRace
open PTX TcMma

example {L : Launch} {X : Execution} (hc : ∀ e c, ¬ X.CpIssue e c)
    (hs : ∀ e s, ¬ X.ShiftIssue e s)
    (hmo : ∀ {x y : EvId} {cell : Cell} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
      {mask mask' : List Nat}, X.MmaCell x cell → X.MmaCell y cell →
      X.MmaIssue x d s acc mask → X.MmaIssue y d' s' acc' mask' →
      x.1 < L.threads ∧ x.1 = y.1 ∧ SameAccumulator d s d' s')
    (hso : ∀ {x y : EvId} {cell : Cell}, StoreCell L X x cell → StoreCell L X y cell →
      x.1 < L.threads ∧ x.1 = y.1)
    (hms : ∀ {x y : EvId} {cell : Cell}, X.MmaCell x cell → StoreCell L X y cell →
      Before L X x y ∨ StoreDoneBefore L X y x) :
    ¬ WritesUnsafe L X :=
  writesSafe_of hc hs (mm_of_po hmo) hms (ss_of_po hso)

end PTX.Tests.TmemRace
