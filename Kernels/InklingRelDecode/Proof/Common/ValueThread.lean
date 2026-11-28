-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Lemmas.Flow.EraseGlueHead
public import Kernels.InklingRelDecode.Proof.Prologue.Export.Value
public import Kernels.InklingRelDecode.Proof.Softmax.Export.Value

@[expose] public section

/-! # The value thread machine `threadD`

Every role of `thread` (`Common/Roles.lean`) is a control machine: the data registers are
havocked, so `Follow` never reads a value. `threadD` is the same glue with a value machine in the
slot of each data role (Prologue, Softmax, Epilogue), laid over its control machine. A slot's
machine erases to its control machine (`Code.Erases`, `Lemmas/Flow/Erase.lean`,
`Lemmas/Flow/EraseGlueHead.lean`): the same first state, and every step it follows is the control
machine's step on the erased states.

**The slots.** A value lane replaces its slot's body by its role's value machine and the slot's
erasure by the machine's control projection, and proves the slot's steps and first state. Until
then the slot is the control machine (the `id` erasure). `thread` and every statement above it are
untouched: `control_of_data` brings a followed value state down to the control state on the same
prefix of the trace. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **Slot `Prologue` (values)**. -/
@[reducible] def prologueDCode (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code kernel Assumptions.all L g :=
  Prologue.Data.code Q L g w

/-- **Slot `Prologue` (values)**: the erasure to the control state. -/
def prologueErase (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    (prologueDCode Q L g w).D → (Prologue.Control.checkedCode Q L g w).D := Prologue.Data.D.c

theorem prologue_erases (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code.Erases (prologueDCode Q L g w) (Prologue.Control.checkedCode Q L g w)
      (prologueErase Q L g w) :=
  Prologue.Data.erases Q L g w

/-- **Slot `Softmax` (values)**, at the entry the prologue handed over. -/
@[reducible] def softmaxDCode (e : Softmax.Control.Entry) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Softmax.Data.codeS e L g

/-- **Slot `Softmax` (values)**: the erasure to the control state. -/
def softmaxErase (e : Softmax.Control.Entry) (L : Launch) (g : Nat) :
    (softmaxDCode e L g).D → (Softmax.Control.code e L g).D := Softmax.Data.D.c

theorem softmax_erases (e : Softmax.Control.Entry) (L : Launch) (g : Nat) :
    Code.Erases (softmaxDCode e L g) (Softmax.Control.code e L g) (softmaxErase e L g) :=
  Softmax.Data.erasesS e L g

/-- **Slot `Epilogue` (values)**, at the entry the softmax handed over. -/
@[reducible] def epilogueDCode (e : Epilogue.Control.Entry) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Epilogue.Control.code e L g

/-- **Slot `Epilogue` (values)**: the erasure to the control state. -/
def epilogueErase (e : Epilogue.Control.Entry) (L : Launch) (g : Nat) :
    (epilogueDCode e L g).D → (Epilogue.Control.code e L g).D := id

theorem epilogue_erases (e : Epilogue.Control.Entry) (L : Launch) (g : Nat) :
    Code.Erases (epilogueDCode e L g) (Epilogue.Control.code e L g) (epilogueErase e L g) :=
  Code.Erases.rfl' _

/-- The value machine of the softmax and the epilogue behind it. -/
@[reducible] def softDCode (e : Softmax.Control.Entry) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Code.glue (softmaxDCode e L g) (fun _ : Unit => epilogueDCode (epiEntry e (g % L.block)) L g)
    (fun d => epiExit (softmaxErase e L g d))

/-- The erasure of a value state of the softmax and epilogue. -/
def softErase (e : Softmax.Control.Entry) (L : Launch) (g : Nat) :
    (softDCode e L g).D → (softCode e L g).D :=
  Code.eraseSumH (softmaxErase e L g) (fun _ => epilogueErase _ L g)

theorem soft_erases (e : Softmax.Control.Entry) (L : Launch) (g : Nat) :
    Code.Erases (softDCode e L g) (softCode e L g) (softErase e L g) :=
  Code.Erases.glueHead (softmax_erases e L g) (fun _ => rfl) (fun _ => epilogue_erases _ L g)

/-- **The value machine of a data role**: the prologue's, then the softmax's and the epilogue's. -/
@[reducible] def dataDCode (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code kernel Assumptions.all L g :=
  Code.glue (prologueDCode Q L g w) (fun e => softDCode e L g)
    (fun d => dataExit Q L g w (prologueErase Q L g w d))

/-- The erasure of a value state of a data role. -/
def dataErase (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    (dataDCode Q L g w).D → (dataCode Q L g w).D :=
  Code.eraseSumH (prologueErase Q L g w) (fun e => softErase e L g)

theorem data_erases (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code.Erases (dataDCode Q L g w) (dataCode Q L g w) (dataErase Q L g w) :=
  Code.Erases.glueHead (prologue_erases Q L g w) (fun _ => rfl) (fun e => soft_erases e L g)

/-- The value fragment of each role of the thread (the dispatch roles have no values). -/
@[reducible] def fragD (Q : Params) (L : Launch) (g : Nat) (r : Role) :
    Flow.Code kernel Assumptions.all L g :=
  match r with
  | .dispatch word x => workerCode Q L g word x
  | .prologue word => dataDCode Q L g word

/-- The erasure of a value fragment's state. -/
def eraseFrag (Q : Params) (L : Launch) (g : Nat) :
    ∀ r, (fragD Q L g r).D → (frag Q L g r).D
  | .dispatch _ _ => id
  | .prologue word => dataErase Q L g word

theorem frag_erases (Q : Params) (L : Launch) (g : Nat) :
    ∀ r, Code.Erases (fragD Q L g r) (frag Q L g r) (eraseFrag Q L g r)
  | .dispatch _ _ => Code.Erases.rfl' _
  | .prologue word => data_erases Q L g word

/-- **The value thread machine**: `thread` with the value fragments. -/
@[reducible] def threadD (Q : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g :=
  Code.roleThread (Startup.code Q L g) (fragD Q L g) Startup.Entry.pc Startup.enterOf (sel L g) cls

/-- The erasure of a value thread state. -/
def eraseThread (Q : Params) (L : Launch) (g : Nat) (s : (threadD Q L g).D) :
    (thread Q L g).D :=
  (Code.eraseSum (Code.eraseStubs (eraseFrag Q L g)) s.1, s.2)

theorem thread_erases (Q : Params) (L : Launch) (g : Nat) :
    Code.Erases (threadD Q L g) (thread Q L g) (eraseThread Q L g) :=
  Code.Erases.roleThread (frag_erases Q L g)

/-- **A followed value state erases to the control state** before the same event. -/
theorem control_of_data {Q : Params} {L : Launch} {X : Execution} {g k : Nat}
    {s : (threadD Q L g).D} (hs : Frame.stateAt (threadD Q L) X g k = some (some s)) :
    Frame.stateAt (thread Q L) X g k = some (some (eraseThread Q L g s)) :=
  Frame.stateAt_erase (C' := threadD Q L) (C := thread Q L) (fun g => thread_erases Q L g) hs

end
end PTX.Kernels.InklingRelDecode.Proof
