-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Open

@[expose] public section

/-! # The softmax warps' machine in the thread machine

The softmax fragment (`Softmax.codeD`) steps every state but its 51 numeric ones from the table
(`Softmax.stepAt_ctl`); the numeric ones are the named premise `Softmax.NumSteps`. So that the
thread machine stays sound with no premise, the role's machine in the glue is `codeT`: the data
machine whose invariant also asks the lane to be in warps 0 to 7, and, unless every softmax lane's
numeric steps hold (`NumAll`), excludes the numeric states, a transition into which stops the
machine (`some none`, which the step obligation admits). Under `NumAll` it is the data machine
with the warp condition (`next_eq`), so the softmax warps are followed by the data machine; this
is the only place where `NumAll` enters, as a premise of the following theorems. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The numeric steps of every softmax lane.** -/
def NumAll (p : Params) (L : Launch) : Prop :=
  ∀ g < L.threads, g % L.block / 32 < 8 → NumSteps p L g

/-- A stop instead of a numeric successor. -/
def redirect : Option (Option D) → Option (Option D)
  | some (some d') => if d'.numeric = true then some none else some (some d')
  | x => x

open Classical in
/-- The successor of the role's machine: the data machine's, and without `NumAll` a stop instead
of a numeric state. -/
def nextT (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  if NumAll p L then (codeD p L g).next d e else redirect ((codeD p L g).next d e)

/-- **The softmax warps' machine in the thread machine.** -/
@[reducible] def codeT (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := (codeD p L g).init
  pc := (codeD p L g).pc
  facts := (codeD p L g).facts
  sub := (codeD p L g).sub
  acc := (codeD p L g).acc
  inv := fun d => (codeD p L g).inv d ∧ g % L.block / 32 < 8 ∧ (NumAll p L ∨ d.numeric = false)
  next := nextT p L g

theorem next_eq (hN : NumAll p L) (d : D) (e : Event) :
    (codeT p L g).next d e = (codeD p L g).next d e := by
  simp only [codeT, nextT, hN, ↓reduceIte]

theorem atD_iff {d : D} {t : TState} : (codeT p L g).AtD d t ↔ (codeD p L g).AtD d t := Iff.rfl

/-- An event fired at a state of the role's machine is fired at the same state of the data
machine. -/
theorem fired_D {d : D} {e : Event} {o : Option TState}
    (hf : (codeT p L g).toMachine.Fired (some d) e o) :
    (codeD p L g).toMachine.Fired (some d) e o ∧ g % L.block / 32 < 8 := by
  obtain ⟨t, ⟨hat, hi, hw, -⟩, hfi⟩ := hf
  exact ⟨⟨t, ⟨hat, hi⟩, hfi⟩, hw⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
