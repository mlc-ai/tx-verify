-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Lemmas.Flow.Erase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Machine

@[expose] public section

/-! # The value thread machine `threadD`

Every role of `thread` (`Common/Roles.lean`) is a UB-tolerant control machine: the data
registers are havocked, so `Follow` never reads a value. `threadD` is the same glue with a value
(data) machine in the slot of each role whose values the results read, beside the control one:
warpgroup 2 (`dequantDCode`: the raw and scale words it read and the chunks it stored) and
warpgroup 0 (`wg0DCode`: the softmax statistics and the output). The other roles keep their
control machine (their data is trivial). A slot's data machine erases to its control machine
(`Code.Erases`, `Lemmas/Flow/Erase.lean`): same first state, and every step it follows is the
control machine's step on the erased states.

**The slots.** A value lane replaces its slot's body by its role's data machine
(`<Role>.Data.code`) and the slot's erasure by the machine's projection, and proves in
`Common/DataSound.lean` its steps (`<role>D_steps`) and its first state from the control
machine's (`<role>D_start`). Until then the slot is the control machine (`id` erasure).

`thread` and every statement above it are untouched: `threadD` is a second machine of the same
threads, and `control_of_data` brings a followed value state down to the control state on the
same prefix of the trace. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **Slot `Dequant` (values)**: warpgroup 2's data machine. -/
@[reducible] def dequantDCode (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code kernel Assumptions.all L g :=
  Dequant.Data.code P L g w

/-- **Slot `Dequant` (values)**: the erasure to the control state. -/
def dequantErase (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    (dequantDCode P L g w).D → (dequantCode P L g w).D := Dequant.Data.D.c

theorem dequant_erases (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code.Erases (dequantDCode P L g w) (dequantCode P L g w) (dequantErase P L g w) :=
  Dequant.Data.erases P L g w

/-- **Slot `Wg0` (values)**: warpgroup 0's data machine. -/
@[reducible] def wg0DCode (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code kernel Assumptions.all L g :=
  Wg0.Data.code P L g w

/-- **Slot `Wg0` (values)**: the erasure to the control state. -/
def wg0Erase (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    (wg0DCode P L g w).D → (wg0Code P L g w).D := Wg0.Data.D.c

theorem wg0_erases (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code.Erases (wg0DCode P L g w) (wg0Code P L g w) (wg0Erase P L g w) :=
  Wg0.Data.erases P L g w

/-- The value fragment of each entry of the startup's dispatch (warpgroup 1 has no values). -/
@[reducible] def fragD (P : Params) (L : Launch) (g : Nat) :
    Entry → Code kernel Assumptions.all L g
  | .wg0 => wg0DCode P L g (warpW L g)
  | .wg1 => wg1Code P L g
  | .dequant => dequantDCode P L g (warpW L g)

/-- The erasure of a value fragment's state. -/
def eraseFrag (P : Params) (L : Launch) (g : Nat) : ∀ r, (fragD P L g r).D → (frag P L g r).D
  | .wg0 => wg0Erase P L g (warpW L g)
  | .wg1 => id
  | .dequant => dequantErase P L g (warpW L g)

theorem frag_erases (P : Params) (L : Launch) (g : Nat) :
    ∀ r, Code.Erases (fragD P L g r) (frag P L g r) (eraseFrag P L g r)
  | .wg0 => wg0_erases P L g _
  | .wg1 => Code.Erases.rfl' _
  | .dequant => dequant_erases P L g _

/-- **The value thread machine**: `thread` with the value fragments. -/
@[reducible] def threadD (P : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  Code.roleThread (startupCode P L g) (fragD P L g) Entry.pc (startupEnter P L g) (sel P L g) cls

/-- The erasure of a value thread state. -/
def eraseThread (P : Params) (L : Launch) (g : Nat) (s : (threadD P L g).D) :
    (thread P L g).D :=
  (Code.eraseSum (Code.eraseStubs (eraseFrag P L g)) s.1, s.2)

theorem thread_erases (P : Params) (L : Launch) (g : Nat) :
    Code.Erases (threadD P L g) (thread P L g) (eraseThread P L g) :=
  Code.Erases.roleThread (frag_erases P L g)

/-- **A followed value state erases to the control state** before the same event. -/
theorem control_of_data {P : Params} {L : Launch} {X : Execution} {g k : Nat}
    {s : (threadD P L g).D} (hs : Frame.stateAt (threadD P L) X g k = some (some s)) :
    Frame.stateAt (thread P L) X g k = some (some (eraseThread P L g s)) :=
  Frame.stateAt_erase (C' := threadD P L) (C := thread P L) (fun g => thread_erases P L g) hs

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
