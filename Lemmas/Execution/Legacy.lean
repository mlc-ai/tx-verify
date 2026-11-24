-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.NoTma

@[expose] public section

/-! A source fragment used by the existing proof adapters. These predicates classify
source instructions; they impose no restrictions on Core or on other kernels. -/
namespace PTX

def Kind.Legacy : Kind → Prop
  | .rd a _ => a.acquire = false
  | .wr a _ => a.release = false
  | .arrive _ _ count release scope => count = 1 ∧ release = true ∧ scope = .cta
  | .wait _ _ _ acquire scope => acquire = true ∧ scope = .cta
  | .nc .. | .bar .. | .shfl .. | .rmw .. | .sreg .. | .exit | .ub .. | .mbInit ..
  | .fenceProxy .. | .copy .. => True
  | .tc (.resource .two ..) => False
  | .tc _ => True
  | _ => False

theorem Kind.legacy_of_plain {kind : Kind} (h : kind.isTma = false) : kind.Legacy := by
  cases kind <;> simp_all [Kind.Legacy,Kind.isTma]

/-- No elect, warp barrier or register request, no `fence.sc`, and no releasing write: appending
such an event adds no collective or register-pool synchronization and no memory synchronization
into an existing event (an acquiring read synchronizes only into itself). -/
def Kind.Ordinary : Kind → Prop
  | .elect .. | .warpBar .. | .setMaxReg .. => False
  | .fence .sc _ => False
  | .wr a _ => a.release = false
  | _ => True

theorem Kind.Legacy.ordinary {kind : Kind} (h : kind.Legacy) : kind.Ordinary := by
  cases kind <;> simp_all [Kind.Legacy, Kind.Ordinary]

/-- Ordinary, and no tensor-core instruction: appending such an event adds no waiting-graph
edge out of an existing event. -/
structure Kind.WaitFree (kind : Kind) : Prop where
  ordinary : kind.Ordinary
  notTc : ∀ k, kind ≠ .tc k

theorem Kind.WaitFree.of_plain {kind : Kind} (h : kind.isTma = false) : kind.WaitFree :=
  ⟨(Kind.legacy_of_plain h).ordinary, fun k he => (by rw [he] at h; cases h)⟩

def Execution.Legacy (X : Execution) : Prop :=
  ∀ i pc kind, X.get i = some ⟨pc,kind⟩ → kind.Legacy

end PTX
