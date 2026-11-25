-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WfInOrder
public import Lemmas.Step.DrainInOrder
public import Lemmas.Step.StoreDone
public import Lemmas.Step.CtaBarAppendWarp

@[expose] public section

/-!
# Assumptions whose execution constraints also restrict elections

Kernel-independent definitions (candidates for `Lemmas/Step/WfInOrder.lean`).

A progress proof extends a consistent execution, and each extension must satisfy the execution
constraint (`Assumption.wf`) of every assumption. The library's interface for this is
`Assumption.WfStep`: the constraints hold of every extension that adds no memory read. That is
false for a kernel with an assumption about the leader an election returns, because an
extension may add an election with another leader. The notion here adds one premise: the
extension adds no election either. The extensions the progress steps build, apart from the
election of a whole warp itself, satisfy it.

* `isElect`, `NoNewElect X Y`: every election event of `Y` is an event of `X`. An extension
  with the same thread events (`noNewElect_of_tr`) and the append of an event that is no
  election (`noNewElect_snoc`) satisfy it.
* `WfStepE sel`: the constraints hold of every extension of a consistent execution that performs
  its new commit arrive-ons in order, adds no memory read and adds no election. The library's
  `Assumption.WfStep` implies it (`WfStepE.of_wfStep`), so every kernel that has the old
  property has the new one.
* The three forms the step lemmas ask for: one appended event (`WfStepE.snoc`), one appended
  event with a record in an object's history (`WfStepE.snocObject`), and an extension with the
  same thread events (`WfSameTr`, from `WfStepE.sameTr`). The last gives the library's premises
  for appended barrier records (`WfSameTr.ctaHistory`) and for the stages of a tensor store
  (`WfSameTr.store`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Step

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X Y Z : Execution}
  {sel : Nat → Bool}

/-- An election event kind. -/
def isElect : Kind → Bool
  | .elect .. => true
  | _ => false

/-- Every election event of `Y` is an event of `X`. -/
def NoNewElect (X Y : Execution) : Prop :=
  ∀ e ev, Y.get e = some ev → isElect ev.kind = true → X.get e = some ev

/-- An extension with the same thread events adds no election. -/
theorem noNewElect_of_tr (h : Y.tr = X.tr) : NoNewElect X Y := by
  intro e ev he _
  unfold Execution.get at he ⊢
  rwa [h] at he

/-- Appending an event that is no election adds no election. -/
theorem noNewElect_snoc {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    (h : isElect e.kind = false) : NoNewElect X (X.snoc g e r) := by
  intro v ev hv hr
  rw [snoc_get] at hv
  split_ifs at hv
  · cases hv
    rw [h] at hr
    cases hr
  · exact hv

/-- Two extensions that add no election compose. -/
theorem NoNewElect.trans (hXY : NoNewElect X Y) (hYZ : NoNewElect Y Z) : NoNewElect X Z :=
  fun e ev he hr => hXY e ev (hYZ e ev he hr) hr

/-- **The assumptions' constraints hold of every extension of a consistent execution that
performs its new commit arrive-ons in order at the sites `sel`, adds no memory read and adds no
election.** -/
def WfStepE (sel : Nat → Bool) (L : Launch) (K : Kernel) (mem0 : Mem0) (A : List Assumption) :
    Prop :=
  ∀ X Y, Consistent L K A mem0 X → X.le Y → X.NotifiedInOrder sel Y → X.NoNewRead Y →
    NoNewElect X Y → ∀ a ∈ A, a.wf L mem0 Y

/-- The library's property implies the one with the extra premise. -/
theorem WfStepE.of_wfStep (h : Assumption.WfStep sel L K mem0 A) : WfStepE sel L K mem0 A :=
  fun X Y hX hle hord hr _ => h X Y hX hle hord hr

/-- An extension that performs no commit arrive-on, adds no read and adds no election keeps the
constraints. -/
theorem WfStepE.quiet (hA : WfStepE sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (hle : X.le Y) (h : Y.tcNotified = X.tcNotified) (hr : X.NoNewRead Y)
    (he : NoNewElect X Y) : ∀ a ∈ A, a.wf L mem0 Y :=
  hA X Y hX hle (Execution.notifiedInOrder_of_eq h) hr he

/-- **One appended event that reads no memory and is no election keeps the constraints.** -/
theorem WfStepE.snoc (hA : WfStepE sel L K mem0 A) (hX : Consistent L K A mem0 X) {g : Nat}
    {e : Event} {r : Nat → Option AsyncCopy.Ref} (hr : e.kind.readsMem = false)
    (he : isElect e.kind = false) : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r) :=
  hA.quiet hX le_snoc rfl (Execution.noNewRead_snoc hr) (noNewElect_snoc he)

/-- **One appended event with a record in an object's history keeps the constraints**, when the
event reads no memory and is no election. -/
theorem WfStepE.snocObject (hA : WfStepE sel L K mem0 A) (hX : Consistent L K A mem0 X)
    {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref} {mb : Loc}
    {rec : MBarrier.Record AsyncCopy.Ref} (hr : e.kind.readsMem = false)
    (he : isElect e.kind = false) : ∀ a ∈ A, a.wf L mem0 (X.snocObject g e r mb rec) :=
  hA.quiet hX (Execution.le_trans le_snoc (Execution.le_appendObject ..)) rfl
    ((Execution.noNewRead_snoc (r := r) hr).trans (Execution.noNewRead_of_tr rfl))
    ((noNewElect_snoc (r := r) he).trans (noNewElect_of_tr rfl))

/-- **The assumptions' constraints hold of every extension with the same thread events** (and
the same commit arrive-ons): the stages of asynchronous operations and appended barrier
records. -/
def WfSameTr (L : Launch) (K : Kernel) (mem0 : Mem0) (A : List Assumption) : Prop :=
  ∀ ⦃X Y : Execution⦄, Consistent L K A mem0 X → X.le Y → Y.tr = X.tr →
    Y.tcNotified = X.tcNotified → ∀ a ∈ A, a.wf L mem0 Y

theorem WfStepE.sameTr (hA : WfStepE sel L K mem0 A) : WfSameTr L K mem0 A :=
  fun _ _ hX hle htr hn =>
    hA.quiet hX hle hn (Execution.noNewRead_of_tr htr) (noNewElect_of_tr htr)

/-- The constraints survive appending records to a CTA barrier's history. -/
theorem WfSameTr.ctaHistory (h : WfSameTr L K mem0 A) :
    Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A :=
  fun X c suffix hX => h hX (X.le_withCtaHistory c ⟨suffix, rfl⟩) rfl rfl

/-- The constraints survive the stages of a tensor store. -/
theorem WfSameTr.store (h : WfSameTr L K mem0 A) :
    Step.StoreDone.WfStoreExtensions L K mem0 A :=
  fun _ _ hX hle htr _ hn => h hX hle htr hn

end PTX.Kernels.FlashKdaFwd.Proof.Progress
