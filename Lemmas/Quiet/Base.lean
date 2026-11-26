-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpAppend
public import Lemmas.Step.CtaBarAppendWarp

@[expose] public section

/-! # Extensions that add no read, no exit and keep the initial bytes

`Assumption.WfStep` asks the assumptions' constraints to survive every in-order extension of a
consistent execution that adds no read. Two kinds of constraint do not:

* a drain constraint such as `TensorStore.ReadsDrainedBeforeExit` fails when an exit is appended
  to a thread whose selected stores have not finished reading their source;
* a read-only constraint such as `Assumption.ncReadOnly` speaks of `Execution.initialByte`, which
  `Execution.le` does not fix.

The progress steps of the library append no exit apart from the exit step itself, and every
extension they build keeps `Execution.initial`. `Assumption.WfQuiet` asks for the constraints only
on such extensions (`Execution.QuietExt`); an exit step asks for the constraints of its own
extension (`Lemmas/Quiet/Released.lean`). `WfStep` with a fixed initial choice implies it only
through `WfQuiet`'s weaker demand: `Assumption.WfStep.wfQuiet`. -/

namespace PTX

/-- The exit event. -/
def Kind.isExit : Kind → Bool
  | .exit => true
  | _ => false

/-- **`Y` adds no read and no exit to `X` and keeps its initial bytes.** -/
structure Execution.QuietExt (X Y : Execution) : Prop where
  noRead : X.NoNewRead Y
  noExit : ∀ e ev, Y.get e = some ev → ev.kind.isExit = true → X.get e = some ev
  initial : Y.initial = X.initial

/-- An extension with the same traces and initial bytes is quiet. -/
theorem Execution.quietExt_of_tr {X Y : Execution} (h : Y.tr = X.tr)
    (hi : Y.initial = X.initial := by exact rfl) : X.QuietExt Y := by
  refine ⟨Execution.noNewRead_of_tr h, fun e ev he _ => ?_, hi⟩
  unfold Execution.get at he ⊢
  rwa [h] at he

/-- Appending an event that is neither a read nor an exit is quiet. -/
theorem Execution.quietExt_snoc {X : Execution} {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (h : e.kind.readsMem = false)
    (hx : e.kind.isExit = false := by exact rfl) : X.QuietExt (X.snoc g e r) := by
  refine ⟨Execution.noNewRead_snoc h, fun v ev hv he => ?_, rfl⟩
  rw [snoc_get] at hv
  split_ifs at hv
  · cases hv
    rw [hx] at he
    cases he
  · exact hv

/-- Two quiet extensions compose. -/
theorem Execution.QuietExt.trans {X Y Z : Execution} (hXY : X.QuietExt Y)
    (hYZ : Y.QuietExt Z) : X.QuietExt Z :=
  ⟨hXY.noRead.trans hYZ.noRead, fun e ev he hx => hXY.noExit e ev (hYZ.noExit e ev he hx) hx,
    hYZ.initial.trans hXY.initial⟩

/-- Appending to several lanes events that are neither reads nor exits is quiet. -/
theorem Execution.quietExt_appendLanes {X : Execution} {ds : List Nat} {ev : Nat → Event}
    (h : ∀ x, (ev x).kind.readsMem = false) (hx : ∀ x, (ev x).kind.isExit = false) :
    X.QuietExt (X.appendLanes ds ev) := by
  refine ⟨noNewRead_appendLanes h, fun i q hq he => ?_, rfl⟩
  rcases appendLanes_get_cases hq with ⟨-, hq'⟩ | ⟨-, -, rfl⟩
  · exact hq'
  · rw [hx] at he
    cases he

/-- **The assumptions' constraints hold of every quiet extension of a consistent execution that
performs its new commit arrive-ons in order at the sites `sel`.** -/
def Assumption.WfQuiet (sel : Nat → Bool) (L : Launch) (K : Kernel) (mem0 : Mem0)
    (A : List Assumption) : Prop :=
  ∀ X Y, Consistent L K A mem0 X → X.le Y → X.NotifiedInOrder sel Y → X.QuietExt Y →
    ∀ a ∈ A, a.wf L mem0 Y

section
variable {sel : Nat → Bool} {L : Launch} {K : Kernel} {mem0 : Mem0} {A : List Assumption}

/-- Constraints that survive every extension without a read survive the quiet ones. -/
theorem Assumption.WfStep.wfQuiet (h : Assumption.WfStep sel L K mem0 A) :
    Assumption.WfQuiet sel L K mem0 A :=
  fun X Y hX hle hord hq => h X Y hX hle hord hq.noRead

/-- A quiet extension of a consistent execution that performs no commit arrive-on keeps the
constraints. -/
theorem Assumption.WfQuiet.quiet (hA : Assumption.WfQuiet sel L K mem0 A) {X : Execution}
    (hX : Consistent L K A mem0 X) {Y : Execution} (hle : X.le Y)
    (h : Y.tcNotified = X.tcNotified) (hr : X.QuietExt Y) : ∀ a ∈ A, a.wf L mem0 Y :=
  hA X Y hX hle (Execution.notifiedInOrder_of_eq h) hr

/-- The constraints survive appending to a CTA's barrier history. -/
theorem Assumption.WfQuiet.ctaHistory (hA : Assumption.WfQuiet sel L K mem0 A) :
    Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A := by
  intro X c suffix hX
  exact hA X _ hX (X.le_withCtaHistory c ⟨suffix, rfl⟩) (Execution.notifiedInOrder_of_eq rfl)
    (Execution.quietExt_of_tr rfl)

end
end PTX
