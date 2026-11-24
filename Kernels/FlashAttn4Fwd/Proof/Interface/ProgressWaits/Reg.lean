-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time

@[expose] public section

/-! # What the thread layer exports for the progress of the register requests

Every role starts with its `setmaxnreg` (`Thread/Role.lean`), at the time `regT` of the site
tables; the prologue's sites are before it and the role's later sites after it
(`Thread/Roles.lean`). A thread blocked at its request waits for the lanes of its warp that have
not requested; the fields place those lanes no later than `regT`, and the blocked thread after
it. Both are facts of each thread's own events and machine states. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The thread layer's facts for the progress of the register requests. -/
structure RegWaitFacts (L : Launch) (X : Execution) : Prop where
  /-- A thread that has made no register request is no later than the requests' time
  (`endTime`): at a prologue state or its role's `setmaxnreg` site, or stopped after a prologue
  event. -/
  before : ∀ {g : Nat}, g < L.threads →
    (∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) →
    endTime L X g ≤ Progress.Time.regT
  /-- After a register request the thread is at a state later than the requests' time. -/
  after : ∀ {g k pc n inst : Nat} {inc : Bool}, g < L.threads →
    X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
    ∃ d, St L X g (k + 1) = some (some d) ∧ Progress.Time.regT < stateTime L g d

end
end PTX.Kernels.FlashAttn4Fwd.Proof
