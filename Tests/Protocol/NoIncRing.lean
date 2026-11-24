-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NoIncRing

/-! # The no-increment ring bound from its parts

`full_phase_le_commits` composed with `commitObj_phase_le_commits` (the empty barrier's phase by
the consumer's commits) and `okPolls_le_phase` (a producer's empty polls by the empty barrier's
phase plus one), the shape of tml-fa4's K/V ring: a full barrier of 64 no-increment arrive-ons
per use, an empty barrier completed by the MMA thread's commits. -/

namespace PTX.Tests.NoIncRing
open PTX PTX.MbarRing AsyncCopy MBarrier

example {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    {F E : Loc} {c d : Nat} (hX : Consistent L K A mem0 X) (o : NoIncObject X F 64)
    (prod : Fin 64 → Nat) (hinj : Function.Injective prod)
    (hsrc : ∀ i, X.AsyncArrive i F true → ∃ a, i.1 = prod a)
    (hlane : ∀ a, (X.tr (prod a)).countP (arriveOnTo F) ≤ Flow.okPolls E (X.tr (prod a)) + d)
    (hu : UnitTx (X.objects E) 0) (hni : NoInval (X.objects E))
    (harr : ∀ {g i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
      X.get (g, i) ≠ some ⟨pc, .arrive E tx cnt rel sc⟩)
    (hcpa : ∀ {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool},
      X.get i = some ⟨pc, .asyncArrive m' noinc⟩ → m' ≠ E)
    (hby : ∀ {i : EvId} {pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16},
      X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp rank = some E →
        i.1 = c ∧ sp.mbar = E ∧ ∀ rank', TcCommit.target sp rank' = some E → rank' = rank)
    {stE : State} (hstE : stateBefore (X.objects E) (X.objects E).length = some stE)
    (hpoll : ∀ a, Flow.okPolls E (X.tr (prod a)) ≤ stE.phase + 1)
    {stF : State} (hstF : stateBefore (X.objects F) (X.objects F).length = some stF) :
    stF.phase ≤ (X.tr c).countP (Flow.commitsTo E) + 1 + d :=
  full_phase_le_commits hX o (by decide) prod hinj hsrc hlane hpoll
    (commitObj_phase_le_commits hX hu hni harr hcpa c hby hstE) hstF

end PTX.Tests.NoIncRing
