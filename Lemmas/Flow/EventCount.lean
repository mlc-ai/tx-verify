-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Polls

@[expose] public section

/-! # Counts of a thread's synchronizing events

A proof tool for run invariants that count a role's events in its trace prefix, next to
`okPolls` and `arrivals`: named-barrier events of a barrier, count and mode (`barEvents`),
Tensor Memory loads and stores at addresses in a range (`tcLdsIn`, `tcStsIn`),
`tcgen05.wait::st` (`tcWaitSts`) and writes at a location (`writesAt`). Each is a `countP`, so
a step adds one exactly when its event matches (`List.countP_append`). -/

namespace PTX.Flow
open PTX

/-- Whether `e` is a named-barrier event on barrier `id` with count `cnt` in mode `m`. -/
def barIs (id cnt : Nat) (m : BarMode) (e : Event) : Bool :=
  match e.kind with
  | .bar id' (some cnt') m' => decide (id' = id ∧ cnt' = cnt ∧ m' = m)
  | _ => false

/-- The named-barrier events on barrier `id` with count `cnt` in mode `m` among `es`. -/
def barEvents (id cnt : Nat) (m : BarMode) (es : List Event) : Nat := es.countP (barIs id cnt m)

/-- Whether `e` is a `tcgen05.ld` at an address in `[lo, hi)`. -/
def tcLdAt (lo hi : Nat) (e : Event) : Bool :=
  match e.kind with
  | .tc (.ld a _ _) => decide (lo ≤ a ∧ a < hi)
  | _ => false

/-- The `tcgen05.ld` events at addresses in `[lo, hi)` among `es`. -/
def tcLdsIn (lo hi : Nat) (es : List Event) : Nat := es.countP (tcLdAt lo hi)

/-- Whether `e` is a `tcgen05.st` at an address in `[lo, hi)`. -/
def tcStAt (lo hi : Nat) (e : Event) : Bool :=
  match e.kind with
  | .tc (.st a _ _) => decide (lo ≤ a ∧ a < hi)
  | _ => false

/-- The `tcgen05.st` events at addresses in `[lo, hi)` among `es`. -/
def tcStsIn (lo hi : Nat) (es : List Event) : Nat := es.countP (tcStAt lo hi)

/-- Whether `e` is a `tcgen05.wait::st`. -/
def isWaitSt (e : Event) : Bool :=
  match e.kind with
  | .tc .waitSt => true
  | _ => false

/-- The `tcgen05.wait::st` events among `es`. -/
def tcWaitSts (es : List Event) : Nat := es.countP isWaitSt

/-- Whether `e` is a write at location `l`. -/
def writeAt (l : Loc) (e : Event) : Bool :=
  match e.kind with
  | .wr a _ => decide (a.loc = l)
  | _ => false

/-- The writes at location `l` among `es`. -/
def writesAt (l : Loc) (es : List Event) : Nat := es.countP (writeAt l)

end PTX.Flow
