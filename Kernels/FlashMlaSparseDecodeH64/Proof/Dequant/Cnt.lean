-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Lemmas.Flow.Counted

@[expose] public section

/-! # Warpgroup 2's ledger classes

The definitions of `Dequant/Ledger.lean`, apart from its step facts (the glued machine's classes
`Cls` import only these). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the ledger. -/
inductive Cnt where
  /-- mbarrier arrivals on an object. -/
  | arrive (l : Loc)
  /-- Successful polls of an object. -/
  | acq (l : Loc)
  /-- Named-barrier arrivals on an id. -/
  | bar (id : Nat)
  /-- Memory stores. -/
  | st
  /-- Undefined behaviour. -/
  | ub
  deriving DecidableEq, Repr

/-- An event at a pc of the role's code. -/
def inRole (e : Event) : Bool := decide (2606 ≤ e.pc ∧ e.pc ≤ 3610)

/-- The class of an event's kind, if any (a failed poll, a load and a fence are in none). -/
def kindOf (e : Event) : Option Cnt :=
  match e.kind with
  | .arrive m .. => some (.arrive m)
  | .wait m _ true .. => some (.acq m)
  | .bar i .. => some (.bar i)
  | .wr .. => some .st
  | .ub _ => some .ub
  | _ => none

/-- **The classes of an event**: its kind class, at a pc of the role. -/
def cls (c : Cnt) (e : Event) : Bool := inRole e && decide (kindOf e = some c)

/-- An event outside the role's pcs is in no class. -/
theorem cls_of_not_inRole {e : Event} (h : inRole e = false) (c : Cnt) : cls c e = false := by
  simp [cls, h]

/-- Warpgroup 2's machine (for the warp word `w`) with its ledger. -/
abbrev MC (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Flow.Code kernel Assumptions.all L g :=
  (Control.code P L g w).counted cls

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
