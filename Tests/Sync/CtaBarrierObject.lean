-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierHistory

namespace PTX.CtaBarrier.Tests

private def arrivals (block id : Nat) (count : Option Nat) (ws : List Nat) :
    Except Error State := ws.foldlM (fun s w => arrive block s id w count) {}

private def slot (r : Except Error State) (id : Nat) : Option Slot :=
  match r with
  | .ok s => some (s.slots id)
  | .error _ => none

-- A 128-thread barrier in a 384-thread CTA: participants need not be the first warps.
example : (slot (arrivals 384 3 (some 128) [4, 5, 6, 7]) 3).map Slot.generation =
    some 1 := by decide

-- Three arrivals cannot satisfy a request for four warps.
example : (slot (arrivals 384 3 (some 128) [4, 5, 6]) 3).map Slot.generation =
    some 0 := by decide

-- Completion resets the same resource for a fresh generation and different participants.
example : (slot (arrivals 384 3 (some 128) [4, 5, 6, 7, 8, 9, 10, 11]) 3).map
    Slot.generation = some 2 := by decide

-- Other resources do not advance when this resource completes.
example : (slot (arrivals 384 3 (some 128) [4, 5, 6, 7]) 2).map Slot.generation =
    some 0 := by decide

example : target 384 (some 128) = .ok 4 := rfl
example : target 384 (some 127) = .error .badCount := rfl
example : target 384 (some 0) = .ok 12 := rfl

-- Repeating an arrival before completion cannot count as another warp.
example : (arrivals 64 0 (some 64) [0, 0]).isOk = false := by decide

-- An arrival at a fresh barrier does not complete a full CTA barrier prematurely.
example : (slot (arrivals 64 0 none [0]) 0).map Slot.generation = some 0 := by decide

-- Once all other lanes have exited, the remaining warp can complete a whole CTA barrier.
private def lastWarp : State := { exited := (Finset.range 32).image (· + 32) }
example : (slot (arrive 64 lastWarp 0 0 none) 0).map Slot.generation = some 1 := by decide

-- A different ID's first arrival belongs to its own generation, regardless of
-- how many times this warp has already used another barrier.
private def differentIds : Except Error State := do
  let s ← arrive 64 {} 1 0 (some 32)
  arrive 64 s 2 0 (some 64)

example : (slot differentIds 1).map Slot.generation = some 1 := by decide
example : (slot differentIds 2).map Slot.generation = some 0 := by decide

private def mismatchedCounts : Except Error State := do
  let s ← arrive 128 {} 1 0 (some 64)
  arrive 128 s 1 1 (some 128)

example : mismatchedCounts.isOk = false := by decide

-- No cross-ID completion: one warp waiting on each of two full-CTA barriers
-- leaves both resources pending.
private def separateWaits : Except Error State := do
  let s ← arrive 64 {} 1 0 none
  arrive 64 s 2 1 none

example : (slot separateWaits 1).map Slot.generation = some 0 := by decide
example : (slot separateWaits 2).map Slot.generation = some 0 := by decide

-- Exiting the last missing live lane releases an already waiting barrier.
private def beforeLastExit : State := {
  exited := (Finset.range 31).image (· + 32)
  slots := fun id => if id = 0 then { expected := some 2, arrived := {0} } else {}
}

example : (slot (exitThread 64 beforeLastExit 63) 0).map Slot.generation = some 1 := by
  decide
example : (slot (exitThread 64 beforeLastExit 63) 1).map Slot.generation = some 0 := by
  decide
example : (exitThread 64 beforeLastExit 32).isOk = false := by decide
example : (arrive 64 {} 16 0 none).isOk = false := by decide

end PTX.CtaBarrier.Tests
