-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.WarpColl

@[expose] public section

/-! # What a warp's class says about the release of its lanes -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Of two lanes of a warp at a collective with as many collectives made, when one is released,
the other is, or an extension is counted. The clock of the state before the other's last event,
when it is at no collective, is below the first lane's. -/
def WarpRel (Q : Params) (L : Launch) (m : Mem0) (X : Execution) (P : Nat → Prop) : Prop :=
  ∀ {x y} {σ : ((schedule Q L).code x).D} {σ' : ((schedule Q L).code y).D},
    P x → P y → SameWarp L x y →
    Frame.stateAt (schedule Q L).code X x (X.tr x).length = some (some σ) → CollAt Q L x σ →
    Frame.stateAt (schedule Q L).code X y (X.tr y).length = some (some σ') →
    CollAt Q L y σ' → (X.tr y).countP Sched.isWarpColl = (X.tr x).countP Sched.isWarpColl →
    (∀ k {σ0 : ((schedule Q L).code y).D}, k + 1 = (X.tr y).length →
      Frame.stateAt (schedule Q L).code X y k = some (some σ0) → ¬ CollAt Q L y σ0 →
      (schedule Q L).time y σ0 < (schedule Q L).time x σ) →
    Step.Released L X x → Step.Released L X y ∨ ∃ Y, Consistent L kernel Assumptions.all m Y ∧
      X.le Y ∧ X.size L < Y.size L

/-- A pending lane whose machine stopped is released. -/
def WarpDead (Q : Params) (L : Launch) (X : Execution) (P : Nat → Prop) : Prop :=
  ∀ {y}, P y → Frame.Pending L X y →
    Frame.stateAt (schedule Q L).code X y (X.tr y).length = none → Step.Released L X y


end PTX.Kernels.InklingRelDecode.Proof
