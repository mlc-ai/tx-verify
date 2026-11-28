-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Lemmas.Flow.Counted

@[expose] public section

/-! # Warpgroup 0's ledger classes

The definitions of `Wg0/Ledger.lean`, apart from its step facts (a glued machine's classes import
only these). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the ledger. -/
inductive Cnt where
  /-- mbarrier arrivals on an object. -/
  | arrive (l : Loc)
  /-- Polls of an object (successful or not). -/
  | wait (l : Loc)
  /-- Successful polls of an object. -/
  | acq (l : Loc)
  /-- Named-barrier events on an id. -/
  | bar (id : Nat)
  /-- Tensor Memory loads. -/
  | tcLd
  /-- Tensor Memory stores. -/
  | tcSt
  /-- TMA tensor stores. -/
  | tensorStore
  /-- Bulk-group commits. -/
  | commit
  /-- Undefined behaviour. -/
  | ub
  deriving DecidableEq, Repr

/-- An event at a pc of the role's code (pcs 103–1841; the shared `ret` is no class's). -/
def inRole (e : Event) : Bool := decide (103 ≤ e.pc ∧ e.pc ≤ 1841)

/-- The class of an event's kind, if any (a wait is also in `wait`: see `cls`). -/
def kindOf (e : Event) : Option Cnt :=
  match e.kind with
  | .arrive m .. => some (.arrive m)
  | .wait m _ true .. => some (.acq m)
  | .bar i .. => some (.bar i)
  | .tc (.ld ..) => some .tcLd
  | .tc (.st ..) => some .tcSt
  | .tensorStore .. => some .tensorStore
  | .bulkCommit => some .commit
  | .ub _ => some .ub
  | _ => none

/-- The object an event polls, if it is a poll. -/
def waitOf (e : Event) : Option Loc :=
  match e.kind with
  | .wait m .. => some m
  | _ => none

/-- **The classes of an event**: its kind class or its poll's object, at a pc of the role. -/
def cls : Cnt → Event → Bool
  | .wait l, e => inRole e && decide (waitOf e = some l)
  | c, e => inRole e && decide (kindOf e = some c)

/-- An event outside the role's pcs is in no class. -/
theorem cls_of_not_inRole {e : Event} (h : inRole e = false) (c : Cnt) : cls c e = false := by
  cases c <;> simp [cls, h]

/-- Warpgroup 0's control machine with its ledger. -/
abbrev MC (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Flow.Code kernel Assumptions.all L g :=
  (Control.code P L g w).counted cls

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
