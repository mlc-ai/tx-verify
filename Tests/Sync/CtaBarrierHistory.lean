-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.CtaBarrierHistory

namespace PTX.CtaBarrier.Tests

private def warpRecord (id w : Nat) (n : Option Nat) : Record (Nat × Nat) :=
  .arrival id w n ((List.range 32).map fun lane =>
    let g := w * 32 + lane
    (g, (g, 0)))

private def generations (block id : Nat) (h : List (Record (Nat × Nat))) : Option Nat :=
  match run block {} h with
  | .ok s => some (s.slots id).generation
  | .error _ => none

-- Four actual warps complete a 128-thread phase, in a 384-thread CTA.
example : generations 384 3 [warpRecord 3 4 (some 128), warpRecord 3 5 (some 128),
    warpRecord 3 6 (some 128), warpRecord 3 7 (some 128)] = some 1 := by decide

-- An arbitrary subset of lanes cannot manufacture a collective warp arrival.
example : generations 384 3 [.arrival 3 4 (some 32) [(128, (128, 0))]] = none := by
  decide

-- A live lane from a different warp cannot fill the missing participation.
example : generations 64 0 [.arrival 0 0 (some 32)
    ((List.range 32).map fun lane => (lane + 1, (lane + 1, 0))) ] = none := by decide

-- The second warp's first-ever use belongs to generation 1, after warp 0 completed 0.
example : generations 64 3 [warpRecord 3 0 (some 32), warpRecord 3 1 (some 32)] =
    some 2 := by decide

-- An exited lane need not contribute an arrival event.
example : generations 32 0 [.exit 31 (31, 0), .arrival 0 0 none
    ((List.range 31).map fun lane => (lane, (lane, 0)))] = some 1 := by decide

end PTX.CtaBarrier.Tests
