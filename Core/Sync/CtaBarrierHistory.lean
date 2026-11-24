-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.CtaBarrierObject

@[expose] public section

namespace PTX.CtaBarrier

/-! ## OBJ-CTA-BARRIER-HISTORY — actual arrivals identify barrier generations

Statement: The history of a CTA's barrier resources lists their updates in order: the collective
  arrivals of whole warps and the exits of threads. The generation of an arrival is the generation
  of its resource just before that update, so it does not depend on how many barriers a thread has
  met earlier. A generation is released by the update that completes it.

Defs: CtaBarrier.Record, CtaBarrier.Record.refs, CtaBarrier.Record.perform, CtaBarrier.run,
  CtaBarrier.At, CtaBarrier.GenerationOf, CtaBarrier.Released, CtaBarrier.CompletesAt

Source:
- §9.7.15.1 (warp arrivals and resource reuse)
- §9.7.14.7 (exited threads)

Direction: reading

Applies: One CTA's named barrier resources and exits

Premises: Each arrival records exactly the non-exited lanes of its warp; event references must
  separately match the source execution.

Effect: Associates actual source-event references with object generations and their release. The
  history orders resource updates. It does not order memory instructions or thread returns. A
  partial warp arrival may be present in a thread trace before there is a collective record; its
  barrier cannot return until its collective record and phase release exist. The execution adapter
  is responsible for reference provenance, uniqueness, source ordering, and the dependence of a
  collective arrival on every recorded lane.
-/

/-- One update of the barrier resources of a CTA, naming its source events by references of type
`α`: the collective arrival of one warp (its barrier number, warp, count and arriving lanes), or
the exit of a thread. -/
inductive Record (α : Type) where
  | arrival (id warp : Nat) (count : Option Nat) (lanes : List (Nat × α))
  | exit (thread : Nat) (ref : α)

/-- Each source event may account for at most one resource update. -/
def Record.refs {α : Type} : Record α → List α
  | .arrival _ _ _ lanes => lanes.map Prod.snd
  | .exit _ e => [e]

/-- Validate the collective before updating the named resource. Lane numbers are
CTA-local thread indices, not positions in the list. -/
def Record.perform {α : Type} (block : Nat) (s : State) : Record α → Except Error State
  | .exit g _ => exitThread block s g
  | .arrival id warp count lanes =>
    if (lanes.map Prod.fst).Nodup ∧
        (∀ p ∈ lanes, p.1 < block ∧ p.1 / 32 = warp ∧ p.1 ∉ s.exited) ∧
        (∀ lane ∈ Finset.range 32,
          let g := warp * 32 + lane
          g < block → g ∉ s.exited → g ∈ lanes.map Prod.fst) then
      arrive block s id warp count
    else .error .badWarp

/-- Apply the records of a history in order, from the state of the first. -/
def run {α : Type} (block : Nat) (s : State) : List (Record α) → Except Error State
  | [] => .ok s
  | r :: rs => (r.perform block s).bind fun t => run block t rs

/-- State just before record `i`, computed from the history rather than assumed. -/
def At {α : Type} (block : Nat) (h : List (Record α)) (i : Nat) (s : State) : Prop :=
  run block {} (h.take i) = .ok s

/-- A source arrival's generation is read from the resource, not a thread ordinal. -/
def GenerationOf {α : Type} (block : Nat) (h : List (Record α))
    (e : α) (id generation : Nat) : Prop :=
  ∃ i s warp count lanes g, h[i]? = some (.arrival id warp count lanes) ∧
    At block h i s ∧ (g, e) ∈ lanes ∧ (s.slots id).generation = generation ∧
    ∃ t, Record.perform block s (.arrival id warp count lanes) = .ok t

/-- The particular resource update which completes a generation. -/
def CompletesAt {α : Type} (block : Nat) (h : List (Record α))
    (i id generation : Nat) : Prop :=
  ∃ r s t, h[i]? = some r ∧ At block h i s ∧ r.perform block s = .ok t ∧
    (s.slots id).generation = generation ∧ (t.slots id).generation = generation + 1

/-- Completion is a specific update in the history, preserved by later updates. -/
def Released {α : Type} (block : Nat) (h : List (Record α))
    (id generation : Nat) : Prop :=
  ∃ i, CompletesAt block h i id generation

end PTX.CtaBarrier
