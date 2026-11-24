-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.ClusterBarrierObject

namespace PTX.ClusterBarrier.Tests

private def run (n : Nat) : State → List Action → Outcome
  | s, [] => .done s
  | s, a :: actions => match perform n s a with
    | .done t => run n t actions
    | other => other

private def phaseOf : Outcome → Option Nat
  | .done s => some s.phase
  | _ => none

private def blocked : Outcome → Bool
  | .blocked => true
  | _ => false

private def errorOf : Outcome → Option Error
  | .fault e => some e
  | _ => none

example : blocked (run 2 {} [.arrive 0, .wait 0]) = true := by decide
example : phaseOf (run 2 {} [.arrive 0, .arrive 1, .wait 0]) = some 1 := by decide

-- A late waiter observes its own old arrival, even after another thread starts round 1.
example : phaseOf (run 2 {} [.arrive 0, .arrive 1, .wait 0, .arrive 0,
    .wait 1, .arrive 1, .wait 0, .wait 1]) = some 2 := by decide

-- Exited participants do not leave the remaining cluster threads permanently blocked.
example : phaseOf (run 2 {} [.arrive 0, .exit 1, .wait 0]) = some 1 := by decide
example : phaseOf (run 2 {} [.arrive 0, .exit 1, .wait 0, .arrive 0, .wait 0]) =
    some 2 := by decide

-- A second arrival before the phase completes is a fault (§9.7.15.3).
example : errorOf (run 2 {} [.arrive 0, .arrive 0]) = some .earlyArrival := by decide
-- After completion a thread may arrive again without waiting; its wait then observes the
-- phase of that later arrival.
example : phaseOf (run 2 {} [.arrive 0, .arrive 1, .arrive 0]) = some 1 := by decide
example : phaseOf (run 2 {} [.arrive 0, .arrive 1, .arrive 0, .arrive 1, .wait 0]) =
    some 2 := by decide
example : blocked (run 2 {} [.arrive 0, .arrive 1, .arrive 0, .wait 0]) = true := by decide
-- A wait of a thread that has not arrived stays blocked: it is no fault (§9.7.15.3).
example : blocked (run 2 {} [.wait 0]) = true := by decide
example : blocked (run 2 {} [.arrive 1, .wait 0]) = true := by decide
-- A repeated wait for one arrival returns, with the phase of that arrival.
example : phaseOf (run 2 {} [.arrive 0, .arrive 1, .wait 0, .wait 0]) = some 1 := by decide
example : errorOf (run 2 {} [.arrive 0, .arrive 1, .wait 0, .wait 0]) = none := by decide
example : errorOf (run 2 {} [.exit 1, .arrive 1]) = some .badThread := by decide
example : errorOf (run 2 {} [.arrive 2]) = some .badThread := by decide

-- Relaxed arrival does not change counter completion (its memory effect is separate).
example : phaseOf (run 2 {} [.arrive 0 false, .arrive 1, .wait 0]) = some 1 := by decide

end PTX.ClusterBarrier.Tests
