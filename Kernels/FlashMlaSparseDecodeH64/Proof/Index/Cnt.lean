-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Lemmas.Flow.Counted

@[expose] public section

/-! # The index warp's ledger classes

The definitions of `Index/Ledger.lean` apart from its step facts (the glued machine's classes
`Cls` import only these): the mbarrier arrivals and successful polls on each object, the
named-barrier arrivals, the shared stores and undefined behaviour, each at a pc of the role's
code (`inRole`, pcs 2332–2586). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the index warp's ledger. -/
inductive Cnt where
  /-- mbarrier arrivals on an object. -/
  | arrive (l : Loc)
  /-- Successful polls of an object. -/
  | acq (l : Loc)
  /-- Named-barrier arrivals on an id. -/
  | bar (id : Nat)
  /-- Memory stores (the coordinate pairs and validity bytes). -/
  | st
  /-- Undefined behaviour. -/
  | ub
  deriving DecidableEq, Repr

/-- An event at a pc of the index code. -/
def inRole (e : Event) : Bool := decide (2332 ≤ e.pc ∧ e.pc ≤ 2586)

/-- The class of an event's kind, if any (a failed poll, a load and a shuffle are in none). -/
def kindOf (e : Event) : Option Cnt :=
  match e.kind with
  | .arrive m .. => some (.arrive m)
  | .wait m _ true .. => some (.acq m)
  | .bar i .. => some (.bar i)
  | .wr .. => some .st
  | .ub _ => some .ub
  | _ => none

/-- **An event's classes**: the class of its kind, when it is at a pc of the index code. -/
def cls (c : Cnt) (e : Event) : Bool := inRole e && decide (kindOf e = some c)

/-- No class holds an event at a pc outside the index code. -/
theorem cls_outside {e : Event} (h : inRole e = false) (c : Cnt) : cls c e = false := by
  simp [cls, h]

/-- The index warp's machine counting its classes. -/
abbrev IC (P : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  (code P L g).counted cls

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
