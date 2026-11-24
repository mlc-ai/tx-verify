-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! # Extensions that keep the assumptions' well-formedness

A proof tool for progress. A progress proof builds extensions of a consistent execution, and each
extension must satisfy the well-formedness constraint of every kernel assumption
(`Consistent.asm`). `Assumption.WfFree` asks that the assumptions constrain no execution. Some
assumptions do constrain executions:

* the commit-order assumption (ASM-COMMIT-ORDER) asks that a selected commit's arrive-on at a rank
  be performed whenever the arrive-on at that rank of the issuing thread's next commit is. Its
  constraint survives every extension that performs its new arrive-ons in issue order;
* an assumption about the bytes that reads at named sites return (as `ncReadOnly`) constrains the
  reads of an execution. Its constraint survives every extension that adds no read, and an
  extension that adds a read keeps it only for the bytes that read returns, which the step that
  builds the read chooses.

The progress side therefore asks for the constraints only on the extensions the step lemmas build.

* `Kind.readsMem`: the thread events that return bytes of memory (a generic-proxy read, an
  `ld.global.nc` read, an atomic).
* `Execution.NoNewRead X Y`: every such event of `Y` is an event of `X`. An extension with the same
  traces (`noNewRead_of_tr`) and the append of an event that reads no memory (`noNewRead_snoc`)
  satisfy it.
* `Execution.NotifiedInOrder sel X Y`: every commit arrive-on that `Y` performs beyond `X` follows,
  in `Y`, the arrive-on at the same rank of the previous commit of its thread, when that commit is
  at a site in `sel`. An extension that performs no arrive-on satisfies it
  (`notifiedInOrder_of_eq`).
* `Assumption.WfStep sel`: the assumptions' constraints hold of every extension of a consistent
  execution that performs its new commit arrive-ons in order and adds no read. The step lemmas that
  build extensions take it in place of `Assumption.WfFree`; a step that adds a read
  (`Step.read_source_counted_extension`) asks for the constraints of its own extension, given the
  sources of the bytes it reads.
* `Assumption.WfInOrder sel`, the strong form: the constraints hold of every extension that
  performs its new commit arrive-ons in order, reads or not. It implies `WfStep`
  (`WfInOrder.step`). -/

namespace PTX

/-- The thread events that return bytes of memory: a generic-proxy read, an `ld.global.nc` read
and an atomic read-modify-write. -/
def Kind.readsMem : Kind → Bool
  | .rd .. | .nc .. | .rmw .. => true
  | _ => false

/-- Every thread event of `Y` that returns bytes of memory is an event of `X`. -/
def Execution.NoNewRead (X Y : Execution) : Prop :=
  ∀ e ev, Y.get e = some ev → ev.kind.readsMem = true → X.get e = some ev

/-- An extension with the same traces adds no read. -/
theorem Execution.noNewRead_of_tr {X Y : Execution} (h : Y.tr = X.tr) : X.NoNewRead Y := by
  intro e ev he _
  unfold Execution.get at he ⊢
  rwa [h] at he

/-- Appending an event that reads no memory adds no read. -/
theorem Execution.noNewRead_snoc {X : Execution} {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (h : e.kind.readsMem = false) :
    X.NoNewRead (X.snoc g e r) := by
  intro v ev hv hr
  rw [snoc_get] at hv
  split_ifs at hv
  · cases hv
    rw [h] at hr
    cases hr
  · exact hv

/-- Two extensions that add no read compose. -/
theorem Execution.NoNewRead.trans {X Y Z : Execution} (hXY : X.NoNewRead Y)
    (hYZ : Y.NoNewRead Z) : X.NoNewRead Z :=
  fun e ev he hr => hXY e ev (hYZ e ev he hr) hr

/-- Every commit arrive-on that `Y` performs beyond `X` follows, in `Y`, the arrive-on at the same
rank of the previous commit of its thread, when that commit is at a site in `sel`. -/
def Execution.NotifiedInOrder (sel : Nat → Bool) (X Y : Execution) : Prop :=
  ∀ (e : EvId) (r : Fin 16), r ∈ Y.tcNotified e → r ∉ X.tcNotified e →
    ∀ (j pc : Nat) (sp : TcCommit.Spec), Y.get (e.1, j) = some ⟨pc, .tc (.commit sp)⟩ →
      sel pc = true → j < e.2 → (∀ k, j < k → k < e.2 → ¬ ∃ s, Y.Commit (e.1, k) s) →
      r ∈ Y.tcNotified (e.1, j)

/-- An extension that performs no new commit arrive-on performs its arrive-ons in order. -/
theorem Execution.notifiedInOrder_of_eq {sel : Nat → Bool} {X Y : Execution}
    (h : Y.tcNotified = X.tcNotified) : X.NotifiedInOrder sel Y := by
  intro e r hr hn
  rw [h] at hr
  exact absurd hr hn

/-- **The assumptions' well-formedness constraints hold of every extension of a consistent
execution that performs its new commit arrive-ons in order at the sites `sel` and adds no
read.** -/
def Assumption.WfStep (sel : Nat → Bool) (L : Launch) (K : Kernel) (mem0 : Mem0)
    (A : List Assumption) : Prop :=
  ∀ X Y, Consistent L K A mem0 X → X.le Y → X.NotifiedInOrder sel Y → X.NoNewRead Y →
    ∀ a ∈ A, a.wf L mem0 Y

/-- The assumptions' well-formedness constraints hold of every extension of a consistent
execution that performs its new commit arrive-ons in order at the sites `sel`. -/
def Assumption.WfInOrder (sel : Nat → Bool) (L : Launch) (K : Kernel) (mem0 : Mem0)
    (A : List Assumption) : Prop :=
  ∀ X Y, Consistent L K A mem0 X → X.le Y → X.NotifiedInOrder sel Y → ∀ a ∈ A, a.wf L mem0 Y

/-- Constraints that survive every in-order extension survive the extensions without a read. -/
theorem Assumption.WfInOrder.step {sel : Nat → Bool} {L : Launch} {K : Kernel} {mem0 : Mem0}
    {A : List Assumption} (h : Assumption.WfInOrder sel L K mem0 A) :
    Assumption.WfStep sel L K mem0 A :=
  fun X Y hX hle hord _ => h X Y hX hle hord

end PTX
