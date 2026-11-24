-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.MBarrierObject

namespace PTX.Tests.MBarrierObject
open PTX.MBarrier

/-- Interpret a single object's operations, retaining the final response. -/
def run (ops : List Action) : Except Error Reply :=
  ops.foldlM (fun r a => perform r.state a) ⟨none, none, none⟩

-- Transaction completion may arrive before expect_tx. Three phases complete and
-- the third successful poll has the same parity argument as the first.
example : run [.init 2, .completeTx 64, .arrive 1 64, .arrive 1,
    .pollParity 0 true, .arrive 2, .pollParity 1 true, .arrive 2, .pollParity 0 true] =
    .ok ⟨some ⟨3, 2, 2, 0, true⟩, some true, some 2⟩ := by rfl

example : run [.init 1, .completeTx 64] =
    .ok ⟨some ⟨0, 1, 1, -64, true⟩, none, none⟩ := by rfl

-- A pending transfer prevents phase completion despite every arrival being present.
example : run [.init 1, .arrive 1 64, .pollParity 0 true] =
    .ok ⟨some ⟨0, 1, 0, 64, true⟩, some false, none⟩ := by rfl

-- Initial empty-buffer parity does not fabricate a completed asynchronous task.
example : run [.init 1, .pollParity 1 true] =
    .ok ⟨some ⟨0, 1, 1, 0, true⟩, some true, none⟩ := by rfl

-- A poll may fail even after completion; it then observes nothing.
example : run [.init 1, .arrive 1, .pollParity 0 false] =
    .ok ⟨some ⟨1, 1, 1, 0, false⟩, some false, none⟩ := by rfl

example : run [.init 1, .arrive 1, .arrive 1] =
    .error .precedingPhaseNotObserved := by rfl

example : run [.init 1, .init 1] = .error .alreadyInitialized := by rfl

example : run [.arrive 1] = .error .invalidObject := by rfl

example : run [.init 1, .completeTx (2 ^ 20)] = .error .transactionRange := by rfl

-- The operand is u32; only the resulting signed tx-count is bounded by limit.
-- A large expected count is valid when it compensates an earlier negative count.
example : run [.init 1, .completeTx (2 ^ 20 - 1), .arrive 1 (2 * (2 ^ 20 - 1))] =
    .ok ⟨some ⟨0, 1, 0, 2 ^ 20 - 1, true⟩, none, none⟩ := by rfl

example : run [.init 2, .arrive 1 (2 ^ 20 - 1), .completeTx (2 * (2 ^ 20 - 1))] =
    .ok ⟨some ⟨0, 2, 1, -(2 ^ 20 - 1), true⟩, none, none⟩ := by rfl

example : run [.init 1, .arrive 1 (2 ^ 32)] = .error .countRange := by rfl

example : run [.init 1, .completeTx (2 ^ 20 - 1), .completeTx 1] =
    .error .transactionRange := by rfl

-- arrive.expect_tx after an early completion brings the transaction count back to
-- zero; the phase then completes with that arrival.
example : run [.init 1, .completeTx 16, .arrive 1 16, .pollParity 0 true] =
    .ok ⟨some ⟨1, 1, 1, 0, true⟩, some true, some 0⟩ := by rfl

end PTX.Tests.MBarrierObject
