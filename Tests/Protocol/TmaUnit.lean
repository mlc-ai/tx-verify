-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaUnit

/-! # A one-CTA TMA unit object

The classification of `TmaUnitObject.of_issues` gives an object without invalidation records
(`TmaUnitObject.noInval`), from the facts a kernel states about the issues that name it. -/

namespace PTX.Tests.TmaUnit
open PTX PTX.MbarRing AsyncCopy MBarrier

example {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {m : Loc}
    {prod : Nat → Prop} (hX : Consistent L K A mem0 X) (init : PairTmaRing.InitFirst X m 1)
    (hinval : ∀ i, ¬ X.MbInval i m)
    (harr : ∀ g j pc tx c rel sc, X.get (g, j) = some ⟨pc, .arrive m tx c rel sc⟩ →
      prod g ∧ c = 1 ∧ rel = true)
    (hasync : ∀ i noinc, ¬ X.AsyncArrive i m noinc)
    (hcopy : ∀ i s, X.Copy i s → s.completion ≠ .mbarrier m)
    (hcommit : ∀ i s rank, X.Commit i s → TcCommit.target s rank ≠ some m)
    (hclc : ∀ i sp targets c, X.ClcIssue i sp targets → m ≠ { sp.mbar with cta := c }) :
    NoInval (X.objects m) :=
  (TmaUnitObject.of_issues hX init hinval harr hasync hcopy hcommit hclc).noInval

end PTX.Tests.TmaUnit
