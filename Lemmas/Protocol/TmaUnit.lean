-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PairTmaRing.Hyp

@[expose] public section

/-! # A one-CTA TMA unit object

An mbarrier object of one CTA filled per use by one thread arrival that expects the use's
transaction bytes (`mbarrier.arrive.expect_tx`) and by the completions of the tensor copies that
complete on it (`TmaUnitObject`): every record is its initialization, a poll, an arrival of one
unit by a producer thread, or a tensor copy's completion; the object is initialized first.
`of_issues` gives the classification from the kinds of issue that name the object. A proof tool,
generic over the kernel (promoted from tml-fa4's `Proof2/Lib/TmaUnit.lean`, lane T1; the
library's `PairTmaRing` is the `cta_group::2` pair ring, which does not fit a count-1 object of
one CTA such as tml-fa4's Q stages). -/

namespace PTX.MbarRing

open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {m : Loc}

/-- How a record of a one-CTA TMA unit object arises. -/
inductive TmaUnitSource (X : Execution) (m : Loc) (prod : Nat → Prop) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {p : Nat} {ok : Bool} (ha : r.action = .pollParity p ok)
  | arrive {g j pc tx : Nat} {sc : MbarScope} (hid : r.id = .thread (g, j)) (hg : prod g)
      (he : X.get (g, j) = some ⟨pc, .arrive m tx 1 true sc⟩) (ha : r.action = .arrive 1 tx)
  | tensor {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec} (hid : r.id = .async i (.notify .load))
      (he : X.get i = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = m)
      (ha : r.action = .completeTx (TensorTransfer.bytes sp.descriptor))

/-- **A one-CTA TMA unit object** with producer threads `prod`. -/
structure TmaUnitObject (X : Execution) (m : Loc) (prod : Nat → Prop) : Prop where
  source : ∀ r ∈ X.objects m, TmaUnitSource X m prod r
  init : PairTmaRing.InitFirst X m 1

namespace TmaUnitObject

/-- No record of such an object is an invalidation. -/
theorem noInval {prod : Nat → Prop} (o : TmaUnitObject X m prod) : NoInval (X.objects m) := by
  intro r hr h
  cases o.source r hr with
  | init ha | poll ha | arrive _ _ _ ha | tensor _ _ _ ha => rw [h] at ha; cases ha

/-- **The classification from the issues that name the object**: no invalidation, every thread
arrival is a producer's unit arrival with release semantics, no other completion. -/
theorem of_issues {prod : Nat → Prop} (hX : Consistent L K A mem0 X)
    (init : PairTmaRing.InitFirst X m 1)
    (hinval : ∀ i, ¬ X.MbInval i m)
    (harr : ∀ g j pc tx c rel sc, X.get (g, j) = some ⟨pc, .arrive m tx c rel sc⟩ →
      prod g ∧ c = 1 ∧ rel = true)
    (hasync : ∀ i noinc, ¬ X.AsyncArrive i m noinc)
    (hcopy : ∀ i s, X.Copy i s → s.completion ≠ .mbarrier m)
    (hcommit : ∀ i s rank, X.Commit i s → TcCommit.target s rank ≠ some m)
    (hclc : ∀ i sp targets c, X.ClcIssue i sp targets →
      m ≠ { sp.mbar with cta := c }) :
    TmaUnitObject X m prod where
  init := init
  source r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (hinval _ ⟨_, he⟩).elim
    | @arrive g j pc tx c rel sc hid he ha =>
      obtain ⟨hg, rfl, rfl⟩ := harr g j pc tx c rel sc he
      exact .arrive hid hg he ha
    | wait _ _ ha => exact .poll ha
    | increment _ he _ => exact (hasync _ _ ⟨_, he⟩).elim
    | tensor hid he hm ha => exact .tensor hid he hm ha
    | arriveOn _ he hm _ _ => subst hm; exact (hasync _ _ ⟨_, he⟩).elim
    | bulk _ he hm _ _ => exact (hcopy _ _ ⟨_, he⟩ hm).elim
    | commit _ he hm _ => exact (hcommit _ _ _ ⟨_, he⟩ hm).elim
    | clc _ he hm _ _ => exact (hclc _ _ _ _ ⟨_, he⟩ hm).elim

end TmaUnitObject

end
end PTX.MbarRing
