-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.AsyncMBarrier

@[expose] public section

namespace PTX
noncomputable section

/-! ## OBJ-CLC-ORIGIN — actual requests, arbitration and per-target effects
Statement: Every resolved request, response write and notification comes from an actual cluster
  launch control instruction, and all requests share one arbitration history. A cluster that is
  already running cannot be canceled, and a successful response names a canceled cluster that no
  other request has claimed. A target observes a response only through the notification to its own
  CTA.

Defs: ClcOk, ClcCanceled

Source:
- §9.7.15.18–19

Direction: reading

Applies: Actual CLC request events in the current one-dimensional launch

Premises: All requests share one reachable arbitration state; every resolved request and every
  nonempty effect has an actual issue event. Nonempty thread traces belong to launched clusters when
  CLC is used.

Effect: Consistent.clc and completion observation; ordinary memory read-source and safety checks
  remain independent. A target observes the response through the notification to its own CTA as
  OBJ-MBAR-OBSERVE defines it (`AsyncCopy.Notifies`). Before any CLC request, arbitration may
  remain implicit. Once a request appears, every nonempty trace's cluster must be recorded as
  launched, which also prevents canceling an earlier-started cluster when extending a prefix. Empty
  canceled threads execute no exit; ClcCanceled accounts for them in the completion definition.
-/
/-- The cluster launch control state of the execution is consistent: one reachable arbitration
state, every request and effect backed by an issuing instruction, each request's effects valid,
and every nonempty thread trace in a launched cluster once a request appears. -/
def ClcOk (L : Launch) (X : Execution) : Prop :=
  Clc.ArbitrationOk L X.clcState ∧
  (∀ request answer, X.clcState.response request = some answer →
    ∃ i s targets, request = Clc.requestId i ∧ X.ClcIssue i s targets) ∧
  (∀ i, (X.clc i).resolved.isSome ∨ (X.clc i).written.Nonempty ∨ (X.clc i).notified.Nonempty →
    ∃ s targets, X.ClcIssue i s targets) ∧
  (∀ i s targets, X.ClcIssue i s targets →
    Clc.EffectsOk L i s X.clcState (X.clc i) ∧
    targets.Nodup ∧ (∀ c, c ∈ targets ↔ Clc.Target L i s c)) ∧
  ((∃ i s targets, X.ClcIssue i s targets) → ∀ g < L.threads, X.tr g ≠ [] →
    X.clcState.owner (L.clusterOfCta (g / L.block)) = some .launched)

/-- Thread `g` belongs to a canceled cluster, so it executes no instruction. -/
def ClcCanceled (L : Launch) (X : Execution) (g : Nat) : Prop :=
  X.tr g = [] ∧ ∃ request,
    X.clcState.owner (L.clusterOfCta (g / L.block)) = some (.canceled request)

end
end PTX
