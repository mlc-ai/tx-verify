-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Machine
public import Lemmas.Flow.Counted

@[expose] public section

/-! # The TMA warp's ledger classes

The definitions of `Tma/Ledger.lean` apart from its step facts (the glued machine's classes `Cls`
import only these): the gathers on each mbarrier, the mbarrier arrivals and successful polls on
each object, the coordinate reads, the named-barrier arrivals, the elections and undefined
behaviour, each at a pc of the role's code (`inRole`, pcs 2165–2330). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the TMA warp's ledger. -/
inductive Cnt where
  /-- Tensor gathers issued on an mbarrier. -/
  | gather (l : Loc)
  /-- mbarrier arrivals on an object. -/
  | arrive (l : Loc)
  /-- Successful polls of an object. -/
  | acq (l : Loc)
  /-- Elements of the coordinate loads. -/
  | rd
  /-- Named-barrier arrivals on an id. -/
  | bar (id : Nat)
  /-- Elections. -/
  | elect
  /-- Undefined behaviour. -/
  | ub
  deriving DecidableEq, Repr

/-- An event at a pc of the TMA code. -/
def inRole (e : Event) : Bool := decide (2165 ≤ e.pc ∧ e.pc ≤ 2330)

/-- The class of an event's kind, if any (a failed poll and a length read are in none). -/
def kindOf (e : Event) : Option Cnt :=
  match e.kind with
  | .tensorIssue _ s => some (.gather s.mbar)
  | .arrive m .. => some (.arrive m)
  | .wait m _ true .. => some (.acq m)
  | .rd .. => some .rd
  | .bar i .. => some (.bar i)
  | .elect .. => some .elect
  | .ub _ => some .ub
  | _ => none

/-- **An event's classes**: the class of its kind, when it is at a pc of the TMA code. -/
def cls (c : Cnt) (e : Event) : Bool := inRole e && decide (kindOf e = some c)

/-- No class holds an event at a pc outside the TMA code. -/
theorem cls_outside {e : Event} (h : inRole e = false) (c : Cnt) : cls c e = false := by
  simp [cls, h]

/-- The TMA warp's machine counting its classes. -/
abbrev TC (P : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  (code P L g).counted cls

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
