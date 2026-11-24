-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # The interface between the thread layer and the layers above

The layers above the thread layer see the threads only through `ThreadFacts`: what each thread
does along its own events, stated with the abstract state its machine (`codes`) is in before an
event (`stateAt`). The thread layer proves `ThreadFacts` (`Thread/Facts.lean`). -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

/-- The machines of the threads. -/
abbrev codes (A B : Nat) (L : Launch) (g : Nat) : Flow.Code kernel Prod L g := code A B L g

/-- The abstract state of thread `g` before its `k`-th event: `some none` when the machine no
longer follows the thread, `none` after an event into a dead state. -/
abbrev stateAt (A B : Nat) (L : Launch) (X : Execution) (g k : Nat) : Option (Option D) :=
  Frame.stateAt (codes A B L) X g k

/-- The position of a state's event in its thread's trace: the input load, the shared store and
the barrier are events 0, 1 and 2, the read of cell `i` is event `3 + i`, the output store event
259, and the exit follows the barrier or the output store. -/
def D.idx (g : Nat) (d : D) : Nat :=
  match d.site with
  | .input => 0 | .share => 1 | .bar => 2 | .sum => 3 + d.i | .out => 259
  | .exit => if g % 256 = 0 then 260 else 3

/-- The event of a state's site. -/
def SiteEvent (A B : Nat) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .input => ∃ bs, e = ⟨Flow.load_0, .rd { loc := gl (A + 4 * g), size := 4 } bs⟩
  | .share => e = ⟨Flow.store_0,
      .wr { loc := sh (g / 256) (L.sharedBase + 4 * (g % 256)), size := 4 } d.v.toBytes⟩
  | .bar => e = ⟨Flow.bar_0, .bar 0 none⟩
  | .sum => ∃ bs, e =
      ⟨Flow.load_1, .rd { loc := sh (g / 256) (L.sharedBase + 4 * d.i), size := 4 } bs⟩
  | .out => e = ⟨Flow.store_1,
      .wr { loc := gl (B + 4 * (g / 256)), size := 4 } (Assumption.erealValue .f32 d.s).toBytes⟩
  | .exit => e = ⟨Flow.exit_0, .exit⟩

/-- The extended-real reading a read event adds to the accumulator (`0` for any other event). -/
def rdVal : Option Event → EReal
  | some ⟨_, .rd _ bs⟩ => (readVal bs).getD 0
  | _ => 0

/-- Bytes a site's read returned that stop the thread: no 4-byte value for the input load; for a
read of the reduction loop, no extended-real reading, or an add the ideal rule declines. -/
def BadRead (d : D) (bs : List (Option Byte)) : Prop :=
  (d.site = .input ∧ ∀ v, rebuild 3 bs = .ok v → v.bytes ≠ 4) ∨
    (d.site = .sum ∧ ∀ y, readVal bs = some y → Assumption.addEReal d.s y = none)

/-- Per-thread facts of an execution. -/
structure ThreadFacts (A B : Nat) (L : Launch) (X : Execution) : Prop where
  /-- Every launched thread is followed by its machine at each of its events. -/
  tracked : Frame.Tracked (codes A B L) X
  /-- A followed state satisfies its invariant. -/
  inv : ∀ {g k : Nat} {d : D}, g < L.threads → stateAt A B L X g k = some (some d) → Inv d
  /-- An event of a followed thread is its state's event. -/
  event : ∀ {g k : Nat} {e : Event} {d : D}, g < L.threads → X.get (g, k) = some e →
    stateAt A B L X g k = some (some d) → SiteEvent A B L g d e
  /-- A followed state's event is at its position. -/
  index : ∀ {g k : Nat} {d : D}, g < L.threads → k ≤ (X.tr g).length →
    stateAt A B L X g k = some (some d) → k = d.idx g
  /-- Only thread 0 of a CTA reduces. -/
  reducer : ∀ {g k : Nat} {d : D}, g < L.threads → stateAt A B L X g k = some (some d) →
    (d.site = .sum ∨ d.site = .out) → g % 256 = 0
  /-- After the input load, the loaded value is what its bytes rebuild to. -/
  input : ∀ {g k : Nat} {d : D}, g < L.threads → stateAt A B L X g k = some (some d) →
    d.site ≠ .input → ∃ bs, X.get (g, 0) =
      some ⟨Flow.load_0, .rd { loc := gl (A + 4 * g), size := 4 } bs⟩ ∧ rebuild 3 bs = .ok d.v
  /-- In the reduction loop and at the output store, the sum is that of the cells read. -/
  sum : ∀ {g k : Nat} {d : D}, g < L.threads → stateAt A B L X g k = some (some d) →
    (d.site = .sum ∨ d.site = .out) → d.s = ∑ j ∈ Finset.range d.i, rdVal (X.get (g, 3 + j))
  /-- The machine stops only at the exit or after a read whose bytes stop the thread. -/
  dead : ∀ {g k : Nat}, g < L.threads → k ≤ (X.tr g).length → stateAt A B L X g k = none →
    ∃ j d e, j < k ∧ stateAt A B L X g j = some (some d) ∧ X.get (g, j) = some e ∧
      (d.site = .exit ∨ ∃ pc a bs, e = ⟨pc, .rd a bs⟩ ∧ BadRead d bs)
  /-- Undefined behaviour comes after the machine stopped. -/
  ub : ∀ {g k pc : Nat} {f : Fault}, g < L.threads → X.get (g, k) = some ⟨pc, .ub f⟩ →
    stateAt A B L X g k = none

end
end PTX.Kernels.BlockSum.Proof
