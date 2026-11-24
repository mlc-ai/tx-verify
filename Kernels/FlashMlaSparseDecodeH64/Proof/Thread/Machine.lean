-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Idle
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0

@[expose] public section

/-!
# A thread of the FlashMLA kernel as a site machine

A thread runs the prologue, then the role of its warpgroup (and, inside warpgroup 1, of its warp
or lane). The prologue's hand-off states name warpgroup 0, 1 or 2. Warpgroup 0 and 2 each run one
role. Every warp of warpgroup 1 reaches the warp-index broadcast at pc 1843, so the hand-off goes
to a `.head` state there; the broadcast's event then hands warp 4 to the MMA role's election,
warp 5 to `Wg1Tma`, warp 7 to `Wg1Index` and warp 6 to `Wg1Idle`, and a warp the dispatch does
not name is not followed (`some none`). A role's terminal event leads to `done`, the kernel's
single `ret`. Every role's own machine supplies its states, pc, facts, invariant and successor;
this file only composes them.

The hand-off side proofs (the local steps from a hand-off state to a role's first state) are in
the role files: `Prologue.step_handoff`, `Wg1Mma.handoff_tma/index/idle/unelected`,
`Wg1Idle.start_of_entry`, and the analogous `start_of_entry`s.

A hand-off continues only for a thread whose warpgroup it names (`wgOf L g = wg`). For a
warpgroup the thread is not in, the state is unreachable and the machine does not follow the
event (`some none`). The warpgroup-1 head's broadcast likewise continues only when it returns
the thread's own warp index and its validity bit, which the full member mask gives every lane.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Machine
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The abstract state of a thread: the prologue, the warpgroup-1 head, a role, or the final
`ret`. -/
abbrev PSite := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Site

inductive ThreadD where
  | prologue (s : PSite)
  /-- The warpgroup-1 head: the warp-index broadcast at pc 1843, before the warp dispatch. -/
  | head
  | wg0 (d : Wg0.D)
  | mma (d : Wg1Mma.D)
  | tma (d : Wg1Tma.D)
  | index (d : Wg1Index.D)
  | idle (s : Thread.Site)
  | wg2 (d : Wg2.D)
  | done

/-- The program counter of a thread state. -/
def ThreadD.pc (P : Params) (L : Launch) (g : Nat) : ThreadD → Nat
  | .prologue s => _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Site.pc s
  | .head => (Wg1Mma.code P L g).pc Wg1Mma.init
  | .wg0 d => (Wg0.code P L g).pc d
  | .mma d => (Wg1Mma.code P L g).pc d
  | .tma d => (Wg1Tma.code P L g).pc d
  | .index d => (Wg1Index.code P L g).pc d
  | .idle s => (Thread.code L g).pc s
  | .wg2 d => (Wg2.code P L g).pc d
  | .done => 3611

/-- The register facts of a thread state. The head's facts are the MMA role's at its own first
state, which is the broadcast's instruction. -/
def ThreadD.facts (P : Params) (L : Launch) (g : Nat) : ThreadD → List (Nat × Value)
  | .prologue s => _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.facts L g s
  | .head => (Wg1Mma.code P L g).facts Wg1Mma.init
  | .wg0 d => (Wg0.code P L g).facts d
  | .mma d => (Wg1Mma.code P L g).facts d
  | .tma d => (Wg1Tma.code P L g).facts d
  | .index d => (Wg1Index.code P L g).facts d
  | .idle s => (Thread.code L g).facts s
  | .wg2 d => (Wg2.code P L g).facts d
  | .done => []

/-- The sub-step of a thread state. -/
def ThreadD.sub (P : Params) (L : Launch) (g : Nat) : ThreadD → Nat
  | .prologue s => _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Site.sub s
  | .head => (Wg1Mma.code P L g).sub Wg1Mma.init
  | .wg0 d => (Wg0.code P L g).sub d
  | .mma d => (Wg1Mma.code P L g).sub d
  | .tma d => (Wg1Tma.code P L g).sub d
  | .index d => (Wg1Index.code P L g).sub d
  | .idle s => (Thread.code L g).sub s
  | .wg2 d => (Wg2.code P L g).sub d
  | .done => 0

/-- The already-read elements of the current vector instruction, forwarded from its role. -/
def ThreadD.acc (P : Params) (L : Launch) (g : Nat) : ThreadD → List Value
  | .wg0 d => (Wg0.code P L g).acc d
  | .tma d => (Wg1Tma.code P L g).acc d
  | .index d => (Wg1Index.code P L g).acc d
  | .wg2 d => (Wg2.code P L g).acc d
  | _ => []

/-- The invariant of a thread state. The head's is vacuous: the broadcast's step decides the
dispatch, and the MMA role's invariant is stated only at its own first state. -/
def ThreadD.inv (P : Params) (L : Launch) (g : Nat) : ThreadD → Prop
  | .prologue _ => True
  | .head => True
  | .wg0 d => (Wg0.code P L g).inv d
  | .mma d => (Wg1Mma.code P L g).inv d
  | .tma d => (Wg1Tma.code P L g).inv d
  | .index d => (Wg1Index.code P L g).inv d
  | .idle _ => True
  | .wg2 d => (Wg2.code P L g).inv d
  | .done => True

/-- The role a hand-off targets. Warpgroup 1's hand-off lands on the head state at pc 1843,
from which the broadcast dispatches the role. -/
def roleStart (P : Params) (L : Launch) (g : Nat) : Fin 3 → ThreadD
  | ⟨0, _⟩ => .wg0 (Wg0.init P L g)
  | ⟨1, _⟩ => .head
  | ⟨2, _⟩ => .wg2 (Wg2.init P L g)
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- The warpgroup-1 head's dispatch of a thread whose broadcast returned its own warp index:
warp 4 runs the MMA role from its election, warp 5 the raw-KV producer, warp 7 the index role and
warp 6 the idle loop. A warp the dispatch does not name has no state here. -/
def headStart (P : Params) (L : Launch) (g : Nat) : Option ThreadD :=
  if warpOf L g = 4 then some (.mma ⟨.elect, 0⟩)
  else if warpOf L g = 5 then some (.tma (Wg1Tma.init P L g))
  else if warpOf L g = 7 then some (.index (Wg1Index.init P L g))
  else if warpOf L g = 6 then some (.idle (Thread.startSite L g))
  else none

/-- Whether a producer election sends this thread to the idle path. -/
def lostElection (L : Launch) (g : Nat) (e : Event) : Bool :=
  match e.kind with
  | .elect _ _ leader => decide (leader ≠ PTX.laneOf L g)
  | _ => false

/-- The successor of a thread state after event `e`.

The prologue's hand-off continues only to the role of the thread's own warpgroup. The head's
broadcast continues only on the thread's own warp index with its validity bit, to the warp's
dispatch. A role state follows the role's own successor; a role that stops following an event
(`some none`) is followed to `done` at its last site, and not followed otherwise. A role's dead
state (`none`) stays dead, except at the `ret` (the MMA, TMA and idle roles), where the thread
is `done`. -/
def next (P : Params) (L : Launch) (g : Nat) : ThreadD → Event → Option (Option ThreadD)
  | .prologue s, e =>
    match _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next L g s e with
    | some (some s') => some (some (.prologue s'))
    | some none =>
      match s with
      | .handoff wg =>
        some (if wgOf L g = wg.val then some (roleStart P L g wg) else none)
      | _ => some none
    | none => none
  | .head, e =>
    match e.kind with
    | .shfl _ _ _ _ recv ok =>
      some (if recv = b32 (warpOf L g) ∧ ok then
        match headStart P L g with
        | some d => some d
        | none => none
      else none)
    | _ => none
  | .wg0 d, e =>
    match Wg0.next P L g d e with
    | some (some d') => some (some (.wg0 d'))
    | some none =>
      if d.site = Wg0.Site.exit ∨ d.site = Wg0.Site.everyone then some (some .done)
      else some none
    | none => none
  | .mma d, e =>
    match Wg1Mma.next P L g d e with
    | some (some d') => some (some (.mma d'))
    | some none =>
      if d.site = Wg1Mma.Site.elect then some (some (.idle (Thread.startSite L g))) else some none
    | none => if d.site = Wg1Mma.Site.exit then some (some .done) else none
  | .tma d, e =>
    match Wg1Tma.next P L g d e with
    | some (some d') => some (some (.tma d'))
    | some none =>
      if d.site = Wg1Tma.Site.exit then some (some .done)
      else if d.site = Wg1Tma.Site.elect ∧ lostElection L g e = true then
        some (some (.idle (Thread.startSite L g)))
      else some none
    | none => if d.site = Wg1Tma.Site.exit then some (some .done) else none
  | .index d, e =>
    match Wg1Index.next P L g d e with
    | some (some d') => some (some (.index d'))
    | some none =>
      if d.site = Wg1Index.Site.barrier then some (some .done) else some none
    | none => none
  | .idle s, e =>
    match Thread.next L s e with
    | some (some s') => some (some (.idle s'))
    | some none => some none
    | none => if s = Thread.Site.exit then some (some .done) else none
  | .wg2 d, e =>
    match Wg2.next P L g d e with
    | some (some d') => some (some (.wg2 d'))
    | some none => if d.site = Wg2.Site.barrier then some (some .done) else some none
    | none => none
  | .done, _ => none

/-- A thread of the kernel as a code machine. -/
def code (P : Params) (L : Launch) (g : Nat) : PTX.Flow.Code kernel Assumptions.all L g where
  D := ThreadD
  init := .prologue .shfl0
  pc := ThreadD.pc P L g
  facts := ThreadD.facts P L g
  sub := ThreadD.sub P L g
  acc := ThreadD.acc P L g
  inv := ThreadD.inv P L g
  next := next P L g

/-- The thread machine consumed by the execution and protocol layers. -/
def machine (P : Params) (L : Launch) (g : Nat) :
    PTX.Flow.Machine kernel Assumptions.all L g :=
  (code P L g).toMachine

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Machine
