-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Cluster.ClusterRecordSnoc

namespace PTX.ClusterBarrier.Tests

private def phaseOf : Outcome → Option Nat
  | .done s => some s.phase
  | _ => none

private def blocked : Outcome → Bool
  | .blocked => true
  | _ => false

private def errorOf : Outcome → Option Error
  | .fault e => some e
  | _ => none

-- Two CTAs, two live lanes each. References are distinct source-event identifiers.
private def a0 : Record Nat := .arrival 0 0 true [(0, 0), (1, 1)]
private def a1 : Record Nat := .arrival 1 0 true [(2, 2), (3, 3)]
private def w0 : Record Nat := .wait 0 0 [(0, 4), (1, 5)]
private def w1 : Record Nat := .wait 1 0 [(2, 6), (3, 7)]

example : blocked (run 2 2 {} [a0, w0]) = true := by decide
example : phaseOf (run 2 2 {} [a0, a1, w0, w1]) = some 1 := by decide

-- One missing live lane cannot count as a warp arrival or a completed warp wait.
example : errorOf (run 2 2 {} [(.arrival 0 0 true [(0, 0)] : Record Nat)]) =
    some .badWarp := by decide
example : errorOf (run 2 2 {} [a0, a1, .wait 0 0 [(0, 4)]]) =
    some .badWarp := by decide
-- Neither duplicate lanes nor a lane from a different CTA can satisfy rendezvous.
example : errorOf (run 2 2 {} [(.arrival 0 0 true [(0, 0), (0, 1), (1, 2)] : Record Nat)]) =
    some .badWarp := by decide
example : errorOf (run 2 2 {} [(.arrival 0 0 true [(0, 0), (1, 1), (2, 2)] : Record Nat)]) =
    some .badWarp := by decide

-- Exited lanes are excluded, but surviving lanes still have to rendezvous.
example : phaseOf (run 2 2 {} [.exit 1 8, .arrival 0 0 true [(0, 0)], a1,
    .wait 0 0 [(0, 4)], w1]) = some 1 := by decide

-- CTA 0 can start the next round before CTA 1 observes the previous round.
example : phaseOf (run 2 2 {} [a0, a1, w0,
    .arrival 0 0 true [(0, 8), (1, 9)], w1,
    .arrival 1 0 true [(2, 10), (3, 11)],
    .wait 0 0 [(0, 12), (1, 13)], .wait 1 0 [(2, 14), (3, 15)]]) =
    some 2 := by decide

-- A partial last warp stays within its own CTA, not the next CTA's lanes.
example : liveWarp 33 2 {} 0 1 [32] = true := by decide
example : liveWarp 33 2 {} 0 1 [32, 33] = false := by decide
example : liveWarp 33 2 {} 1 1 [65] = true := by decide

-- This extraction only names witnesses. Each use below separately proves that
-- replay returns `done` with that witness, so failure cannot be turned into success.
private def stateOf : Outcome → State
  | .done s => s
  | _ => {}

private theorem done_of_phase {o : Outcome} {p : Nat} (h : phaseOf o = some p) :
    o = .done (stateOf o) := by
  cases o <;> simp_all [phaseOf, stateOf]

-- Source references are tied to the actual generation, with checked replay witnesses.
example : ArrivalOf 2 2 [a0, a1, w0, w1] 0 0 true := by
  refine ⟨0, {}, stateOf (a0.perform 2 2 {}), 0, 0, [(0, 0), (1, 1)],
    0, rfl, rfl, by simp, rfl, ?_⟩
  rfl

example : WaitOf 2 2 [a0, a1, w0, w1] 4 0 := by
  let s := stateOf (run 2 2 {} [a0, a1])
  refine ⟨2, s, stateOf (w0.perform 2 2 s), 0, 0, [(0, 4), (1, 5)],
    0, rfl, ?_, by simp, ?_, ?_⟩
  · exact done_of_phase (p := 1) (by decide)
  · rfl
  · exact done_of_phase (p := 1) (by decide)

private def relaxed0 : Record Nat := .arrival 0 0 false [(0, 0), (1, 1)]
private def relaxed1 : Record Nat := .arrival 1 0 false [(2, 2), (3, 3)]

-- Relaxed still completes the barrier, but cannot create a release synchronization edge.
example : phaseOf (run 2 2 {} [relaxed0, relaxed1, w0, w1]) = some 1 := by decide
example (a w : Nat) : ¬ Synchronizes 2 2 [relaxed0, relaxed1, w0, w1] a w := by
  rintro ⟨phase, ⟨i, s, t, cta, warp, lanes, g, hi, _⟩, _⟩
  have hm := List.mem_of_getElem? hi
  simp [relaxed0, relaxed1, w0, w1] at hm

end PTX.ClusterBarrier.Tests
