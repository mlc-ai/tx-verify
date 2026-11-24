-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderInputSites
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyBarriers
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX

noncomputable section

/-- The role's observed work interval. -/
inductive Phase where
  | startup | selection | priming | warmup | steady | drain | exited | faulted

inductive CachePlane where
  | key | value
  deriving DecidableEq

inductive PacketPeriod where
  | priming | warmup | steady
  deriving DecidableEq

/-- K and V each have one packet form in each part of the pipeline. -/
structure Packet where
  period : PacketPeriod
  plane : CachePlane
  deriving DecidableEq

inductive InputPlane where
  | query | bias

/-- A publish identifies the physical ring slot in the issuing lane's CTA. -/
structure Publication where
  packet : Packet
  slot : Fin 3

/-- The preceding group is closed by its ordinary commit, before its tracked arrival. -/
structure CommittedGroup where
  packet : Packet
  vectors : List AsyncCopy.Spec

/-- State after the observed prefix. Histories are stored newest first. -/
structure D where
  phase : Phase := .startup
  pendingCopies : List AsyncCopy.Spec := []
  lastCommit : Option CommittedGroup := none
  published : List Publication := []
  emptyAcquires : List (Fin 3 × Nat) := []
  queryIssues : Nat := 0
  biasIssues : Nat := 0

/-- The decoded distinctions used by the loader's thread facts. -/
inductive Observation where
  | copy (spec : AsyncCopy.Spec)
  | commit (packet : Packet)
  | publish (value : Publication)
  | emptyAcquire (slot : Fin 3) (parity : Nat)
  | input (plane : InputPlane)
  | other

namespace DecodedObservation

open PTX.Kernels.TmlFa4Fwd.Loader in
def packetOfSite : Fin 6 → Packet
  | 0 => ⟨.priming, .key⟩
  | 1 => ⟨.priming, .value⟩
  | 2 => ⟨.warmup, .key⟩
  | 3 => ⟨.warmup, .value⟩
  | 4 => ⟨.steady, .key⟩
  | 5 => ⟨.steady, .value⟩

open PTX.Kernels.TmlFa4Fwd.Loader in
def observePacket (pc : Nat) (arrival : Bool) : Option Packet :=
  ((List.finRange 6).find? (fun site => copyCommitPc site + (if arrival then 1 else 0) == pc)).map
    packetOfSite

open PTX.Kernels.TmlFa4Fwd.Loader in
def locateSlot (l : Launch) (g : Nat) (target : Loc) (ready : Bool) : Option (Fin 3) :=
  (List.finRange 3).find? (fun slot =>
    target == Prologue.initObject l (g / l.block)
      (if ready then readySlot slot else emptySlot slot))

open PTX.Kernels.TmlFa4Fwd.Loader in
def observeInput (pc : Nat) : Option InputPlane :=
  ((List.finRange 14).find? (fun site => (inputSite site).pc == pc)).map fun site =>
    if (inputSite site).bias then .bias else .query

end DecodedObservation

open DecodedObservation

/-- Interpret an event by its role and operands. Program positions stay inside this interpreter. -/
def observe (l : Launch) (g : Nat) (e : Event) : Observation :=
  match e.kind with
  | .copy spec => .copy spec
  | .asyncCommit => (observePacket e.pc false).elim .other .commit
  | .asyncArrive loc true =>
    match observePacket e.pc true, locateSlot l g loc true with
    | some packet, some slot => .publish ⟨packet, slot⟩
    | _, _ => .other
  | .wait loc parity true true .cta =>
    (locateSlot l g loc false).elim .other (fun slot => .emptyAcquire slot parity)
  | .tensorIssue .. => (observeInput e.pc).elim .other .input
  | _ => .other

def DecodedObservation.eventPhase (e : Event) : Phase :=
  match e.kind with
  | .exit => .exited
  | .ub _ => .faulted
  | _ =>
    if e.pc < 174 then .startup else
    if e.pc < 386 then .selection else
    if e.pc < 917 then .priming else
    if e.pc < 1353 then .warmup else
    if e.pc < 1744 then .steady else .drain

def advance (l : Launch) (g : Nat) (d : D) (e : Event) : D :=
  let d := {d with phase := eventPhase e}
  match observe l g e with
  | .copy spec => {d with pendingCopies := spec :: d.pendingCopies}
  | .commit packet =>
    {d with pendingCopies := [], lastCommit := some ⟨packet, d.pendingCopies.reverse⟩}
  | .publish publication => {d with published := publication :: d.published}
  | .emptyAcquire slot parity => {d with emptyAcquires := (slot, parity) :: d.emptyAcquires}
  | .input .query => {d with queryIssues := d.queryIssues + 1}
  | .input .bias => {d with biasIssues := d.biasIssues + 1}
  | .other => d

theorem advanceCommit {l : Launch} {g : Nat} {d : D} {e : Event} {packet : Packet}
    (h : observe l g e = .commit packet) :
    (advance l g d e).pendingCopies = [] ∧
      (advance l g d e).lastCommit = some ⟨packet, d.pendingCopies.reverse⟩ := by
  simp [advance, h]

theorem advancePublication {l : Launch} {g : Nat} {d : D} {e : Event}
    {publication : Publication} (h : observe l g e = .publish publication) :
    (advance l g d e).published = publication :: d.published := by
  simp [advance, h]

def machine (l : Launch) (g : Nat) : PTX.Flow.Machine kernel Assumptions.all l g :=
  observationMachine l g ({} : D) (advance l g)

/-- Every actual loader trace follows the role machine. -/
theorem sound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    (machine l g).Sound :=
  observationSound hp g ({} : D) (advance l g)

/-- The abstract role state at an event is computed from the actual prefix. -/
def atPrefix (l : Launch) (X : Execution) (g index : Nat) : D :=
  ((X.tr g).take index).foldl (advance l g) {}

/-- The public state, including after a truncated execution, requires no instruction cursor. -/
@[simp] theorem stateAtPrefix (l : Launch) (X : Execution) (g index : Nat) :
    stateAt (machine l g) X index = some (atPrefix l X g index) :=
  observationAfter l g ({} : D) ({} : D) (advance l g) _

theorem fired {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e) :
    ∃ o, (machine l g).Fired (atPrefix l X g index) e o :=
  observationFired hp hX he ({} : D) (advance l g)

theorem prefixStep {l : Launch} {X : Execution} {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e) :
    atPrefix l X g (index + 1) = advance l g (atPrefix l X g index) e := by
  have h : Transition (machine l g) X index e.kind (atPrefix l X g index)
      (advance l g (atPrefix l X g index) e) := ⟨e, he, rfl, stateAtPrefix l X g index, rfl⟩
  have hAfter := h.stateAfter
  rw [stateAtPrefix] at hAfter
  exact Option.some.inj hAfter

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
