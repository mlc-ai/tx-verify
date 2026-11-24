-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Facts

@[expose] public section

/-! # The S-full hand-off (the statement)

Proved by the S channel; the Tensor Memory orders read it as a hypothesis. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- **SFull**: a softmax poll of its stage's S-full object with `u` earlier successful polls
observes the notification of the MMA lane's commit to the object with `u` earlier commits. -/
def SFullHandoff (L : Launch) (X : Execution) : Prop :=
  ∀ {h j pc p : Nat} {acq : Bool} {sc : MbarScope}, h < L.threads → Prologue.warpIndex L h < 8 →
    X.get (h, j) =
      some ⟨pc, .wait (sFull L (h / L.block) (Prologue.warpIndex L h / 4)) p true acq sc⟩ →
    ∃ x s rank ws, X.Commit x s ∧ x.1 / L.block = h / L.block ∧
      s.mbar = sFull L (x.1 / L.block) (Prologue.warpIndex L h / 4) ∧
      sCommits L X x.1 (Prologue.warpIndex L h / 4) x.2 =
        sPolls L X h (Prologue.warpIndex L h / 4) j ∧
      TcCommit.target s rank = some (sFull L (h / L.block) (Prologue.warpIndex L h / 4)) ∧
      rank ∈ X.tcNotified x ∧
      AsyncCopy.WaitObserves X (.async x (.tcNotify rank)) (h, j)
        (sFull L (h / L.block) (Prologue.warpIndex L h / 4)) true ws ∧
      ScopesMeet L .cluster x.1 ws h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
