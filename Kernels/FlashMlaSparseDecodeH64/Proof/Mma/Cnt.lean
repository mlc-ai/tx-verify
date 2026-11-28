-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Machine
public import Lemmas.Flow.Counted

@[expose] public section

/-! # The MMA warp's ledger classes

The definitions of `Mma/Ledger.lean`, apart from its step facts (the glued machine's classes
`Cls` import only these). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the ledger. -/
inductive Cnt where
  /-- TMA tensor copies issued. -/
  | tma
  /-- mbarrier arrivals on an object. -/
  | arrive (l : Loc)
  /-- Successful polls of an object. -/
  | acq (l : Loc)
  /-- `tcgen05.cp` copies. -/
  | cp
  /-- Tensor Core commits to an object. -/
  | commit (l : Loc)
  /-- MMA issues. -/
  | mma
  /-- Named-barrier arrivals on an id. -/
  | bar (id : Nat)
  /-- Elections. -/
  | elect
  /-- Undefined behaviour (the reference invariant is guarded by none so far). -/
  | ub
  deriving DecidableEq, Repr

/-- An event at a pc of the role's code. -/
def inRole (e : Event) : Bool := decide (1853 ≤ e.pc ∧ e.pc ≤ 2160)

/-- The class of an event's kind, if any (a failed poll and a fence are in none). -/
def kindOf (e : Event) : Option Cnt :=
  match e.kind with
  | .tensorIssue .. => some .tma
  | .arrive m .. => some (.arrive m)
  | .wait m _ true .. => some (.acq m)
  | .tc (.cp _) => some .cp
  | .tc (.commit s) => some (.commit s.mbar)
  | .tc (.mma ..) => some .mma
  | .bar i .. => some (.bar i)
  | .elect .. => some .elect
  | .ub _ => some .ub
  | _ => none

/-- **The classes of an event**: its kind class, at a pc of the role. -/
def cls (c : Cnt) (e : Event) : Bool := inRole e && decide (kindOf e = some c)

/-- An event outside the role's pcs is in no class. -/
theorem cls_of_not_inRole {e : Event} (h : inRole e = false) (c : Cnt) : cls c e = false := by
  simp [cls, h]

/-- The MMA warp's machine with its ledger. -/
abbrev MC (P : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  (code P L g).counted cls

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
