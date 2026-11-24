-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace PTX.Tmem

/-! ## OBJ-TMEM-ALLOCATOR — non-exclusive Tensor Memory allocation lifetimes
Statement: Each CTA's Tensor Memory allocator holds a list of live allocations in a 512-column
  address space; an allocation completes only with a range of free columns inside that space, and a
  deallocation removes the live allocation with its address and column count. A `Request` is what
  the instruction names (its operands), and an `Action` is the transition the allocator performs for
  it. `Action.alloc` adds the column the allocator selects when the allocation completes, and it
  adds no extra PTX operand. Each successful allocation gets a fresh logical lifetime id, including
  reuse of the same returned address. An allocator fault occurs when a column count is not 32, 64,
  128, 256 or 512, when an allocation requests more columns than the previous allocation of the CTA,
  when an allocation follows relinquishment of the permit, or when a deallocation matches no live
  allocation.

Defs: Tmem.Region, Tmem.State, Tmem.Request, Tmem.Action, Tmem.Action.request, Tmem.Error,
  Tmem.Outcome, Tmem.validColumns, Tmem.disjoint, Tmem.available, Tmem.perform

Source:
- §9.7.18.1
- §9.7.18.7.1, Table 58

Direction: stricter

Applies: A CTA's non-exclusive 512-column Tensor Memory address space; whole-allocation releases

Premises: Allocation request sizes are valid, non-increasing and made before relinquishing the
  permit. A successful allocation selects an available range; a release identifies a live allocation
  of the same size.

Effect: Local object transitions replayed by OBJ-TMEM-HISTORY. Physical resource progress is a
  separate obligation. `blocked` says that this candidate cannot complete in the current local
  resource state; it does not assert that no other candidate is available and promises no physical
  progress.

Review: `Action.alloc` is the column the allocator selects when the allocation completes
  (§9.7.18.7.1: "The tcgen05.alloc blocks if the requested amount of Tensor Memory is not available
  and unblocks as soon as the requested amount of Tensor Memory becomes available for allocation.").
  The lifetime id is proof metadata and is not a PTX-visible token. Whole-allocation release is a
  sufficient discipline for the represented deallocation operation. A partial release is not
  justified by this object. The scope holds for any allocation count, warp role and tile shape.
  Exclusive allocation permits and peer-CTA collective ownership require their own resource scope.
-/

/-- One live allocation of a CTA's Tensor Memory: its lifetime id, its first column and its
column count. -/
structure Region where
  /-- A fresh number for each successful allocation. It is proof metadata, not a PTX value. -/
  lifetime : Nat
  /-- The first column of the allocation, the address that `tcgen05.alloc` returns. -/
  base : Nat
  /-- The number of allocated columns. -/
  columns : Nat
  deriving DecidableEq, Repr

/-- The state of one CTA's Tensor Memory allocator (§9.7.18.7.1). -/
structure State where
  /-- Whether the CTA still holds the right to allocate. `tcgen05.relinquish_alloc_permit`
  clears it. -/
  permit : Bool := true
  /-- The column count of the previous allocation; later allocations may not request more. -/
  previousColumns : Option Nat := none
  /-- The lifetime id that the next allocation receives. -/
  nextLifetime : Nat := 0
  /-- The live allocations, in allocation order. -/
  live : List Region := []
  deriving DecidableEq, Repr

/-- An allocation-management instruction's operands: an allocation's column count, a release's
address and column count, or permit relinquishment. -/
inductive Request where
  | alloc (columns : Nat)
  | dealloc (base columns : Nat)
  | relinquish
  deriving DecidableEq, Repr

/-- The transition that the allocator performs for one request: an allocation of `columns`
columns at the column `base` that the allocator selected, a deallocation, or relinquishment of
the permit. -/
inductive Action where
  /-- `base` is the allocation result chosen by the allocator. -/
  | alloc (columns base : Nat)
  | dealloc (base columns : Nat)
  | relinquish
  deriving DecidableEq, Repr

/-- The request an allocator transition performs. -/
def Action.request : Action → Request
  | .alloc n _ => .alloc n
  | .dealloc base n => .dealloc base n
  | .relinquish => .relinquish

/-- An allocator fault, each of which the ISA makes undefined behaviour. -/
inductive Error where
  /-- A column count other than 32, 64, 128, 256 or 512. -/
  | invalidColumns
  /-- An allocation requests more columns than the previous allocation of the CTA. -/
  | increasingRequest
  /-- An allocation after the CTA relinquished its allocation permit. -/
  | relinquishedPermit
  /-- No live whole allocation matches this release. -/
  | unmatchedRelease
  deriving DecidableEq, Repr

/-- The result of one allocator transition: the next state, a blocked allocation that cannot
complete in this state, or a fault. -/
inductive Outcome where
  | done (state : State)
  | blocked
  | fault (reason : Error)
  deriving DecidableEq, Repr

/-- Column counts of a non-exclusive allocation (Table 58; §9.7.18.7.1: "the operand nCols must be
a power of 2, in the range [32, 512]"). Used by the `tcgen05.alloc`/`dealloc` instruction rule and
by `perform`. -/
def validColumns (n : Nat) : Bool := n == 32 || n == 64 || n == 128 || n == 256 || n == 512

/-- The column range starting at `base` with `columns` columns does not overlap region `r`. -/
def disjoint (base columns : Nat) (r : Region) : Bool :=
  decide (base + columns ≤ r.base ∨ r.base + r.columns ≤ base)

/-- Candidate result columns lie within the address space and avoid live regions.
The allocation size, rather than an extra alignment assumption on the returned
address, is checked by `validColumns`. -/
def available (s : State) (base columns : Nat) : Bool :=
  decide (base + columns ≤ 512) && s.live.all (disjoint base columns)

/-- The effect of one action on an allocator state. An allocation faults on an invalid column
count, after relinquishment of the permit, or when it requests more columns than the previous
allocation; it blocks when its selected range is not available, and otherwise adds a region with
a fresh lifetime id. A deallocation faults on an invalid column count or when no live region has
its address and column count, and otherwise removes that region. Relinquishment clears the
permit. -/
def perform (s : State) : Action → Outcome
  | .alloc n base =>
    if !validColumns n then .fault .invalidColumns
    else if !s.permit then .fault .relinquishedPermit
    else if s.previousColumns.any (fun previous => previous < n) then .fault .increasingRequest
    else if !available s base n then .blocked
    else .done { s with
      previousColumns := some n
      nextLifetime := s.nextLifetime + 1
      live := s.live ++ [⟨s.nextLifetime, base, n⟩] }
  | .dealloc base n =>
    if !validColumns n then .fault .invalidColumns
    else match s.live.find? (fun r => r.base == base && r.columns == n) with
      | none => .fault .unmatchedRelease
      | some region => .done { s with live := s.live.erase region }
  | .relinquish => .done { s with permit := false }

end PTX.Tmem
