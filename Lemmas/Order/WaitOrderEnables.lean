-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.WaitOrder
public import Lemmas.Order.JointWaits
public import Core.Assembly.Execution
public import Lemmas.Tensor.TensorDescriptor
public import Mathlib.Data.Fintype.Card
public import Lemmas.Async.AsyncCopy

@[expose] public section

/-! # Dependency edges

Tools for the execution-order axioms of `Consistent`: the dependency order (DEP-ORDER) and
object coherence (MEM-OBJECT-ORDER-CAUSALITY). The edges of the dependency order `DepStep`: a
present node's stages (`DepStep.node`), the issue of a stage of the thread's own asynchronous
operation (`DepStep.issue`), and the stage order (`DepStep.stage`). The two remaining edges are
`DepStep.of_witness` (a witness of a need precedes the return that the need blocks) and
`DepStep.of_resumes` (a return precedes the events that depend on it), both in Core.
The dependency steps alone have no cycle when the dependency axiom holds (`DepStepAcyclic`,
`DepStepAcyclic.of_dependency`), and causality alone has none near an object
(`ObjectCoherent.cause`). The position of a present event: `len_of_get`, `present_of_len`. -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

theorem len_of_get {i : EvId} {ev : Event} (h : X.get i = some ev) : i.2 < (X.tr i.1).length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem present_of_len {i : EvId} (h : i.2 < (X.tr i.1).length) : X.RefPresent (.thread i) :=
  ⟨_, List.getElem?_eq_getElem h⟩

end

section
variable {L : Launch} {X : Execution} {K : Kernel}

/-- A present node's issue point precedes its completion point. -/
theorem DepStep.node {e : AsyncCopy.Ref} (h : X.RefPresent e) :
    DepStep L K X (e, false) (e, true) :=
  .inl (Or.inl ⟨rfl, rfl, rfl, h⟩)

/-- The stage order is part of the dependency order. -/
theorem DepStep.stage {a c : AsyncCopy.Ref × Bool} (h : StageOrder X a c) :
    DepStep L K X a c := .inl h

/-- The issue of a thread instruction precedes a stage of the asynchronous operation it issued,
unless the stage is a notification, a bulk store's full completion, an MMA's completion or the
arrive-on of `cp.async.mbarrier.arrive` (`IssueStage`). -/
theorem DepStep.issue {i : EvId} {p : AsyncCopy.Part} (hi : X.RefPresent (.thread i))
    (hp : X.AsyncPresent i p) (hn : ∀ t, p ≠ .notify t) (hd : p ≠ .fullDone) (hm : p ≠ .mmaDone)
    (ha : p ≠ .arriveOn) : DepStep L K X (.thread i, false) (.async i p, false) := by
  refine .inr (.inl ⟨rfl, rfl, i, p, rfl, rfl, hi, hp, ?_⟩)
  cases p <;>
    first
      | exact absurd rfl (hn _)
      | exact absurd rfl hd
      | exact absurd rfl hm
      | exact absurd rfl ha
      | trivial

end

section
variable {L : Launch} {X : Execution} {K : Kernel}

/-- The dependency steps alone have no cycle: `DependencyOk.acyclic` without the order of an
object. -/
def DepStepAcyclic (L : Launch) (K : Kernel) (X : Execution) : Prop :=
  ∀ n, ¬ Relation.TransGen (DepStep L K X) n n

/-- DEP-ORDER: the dependency axiom gives that no dependency step precedes itself. -/
theorem DepStepAcyclic.of_dependency (h : DependencyOk L K X) : DepStepAcyclic L K X :=
  fun n hn =>
    h.acyclic (.mbar ⟨.shared, 0, 0⟩) trivial n (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ hn)

end

/-- Causality alone has no cycle. -/
theorem ObjectCoherent.cause {L : Launch} {X : Execution} (h : ObjectCoherent L X) :
    ∀ n, ¬ Relation.TransGen (stageCausality L X) n n :=
  fun n hn => h (.mbar ⟨.shared, 0, 0⟩) n (Relation.TransGen.mono (fun _ _ => Or.inl) _ _ hn)

end

end PTX
