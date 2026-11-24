-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Facts

@[expose] public section

/-! # The O-full hand-off and the routes of the correction accesses (the statements)

Proved by the O channel and the named barriers; the Tensor Memory orders read them as
hypotheses. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- Commits of lane `g` to stage `st`'s O-full object before its event `i`. -/
def oCommits (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  ((X.tr g).take i).countP (commitsTo (oFull L (g / L.block) st))

/-- **The O-full hand-off**: a correction poll of a stage's O-full object with `u` earlier
successful polls observes the notification of the MMA lane's commit to the object with `u` earlier
commits. -/
def OFullHandoff (L : Launch) (X : Execution) : Prop :=
  ∀ {h j pc p st : Nat} {acq : Bool} {sc : MbarScope}, h < L.threads →
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 → st < 2 →
    X.get (h, j) = some ⟨pc, .wait (oFull L (h / L.block) st) p true acq sc⟩ →
    ∃ x s rank ws, X.Commit x s ∧ x.1 / L.block = h / L.block ∧
      s.mbar = oFull L (x.1 / L.block) st ∧
      oCommits L X x.1 st x.2 = okPolls (oFull L (h / L.block) st) ((X.tr h).take j) ∧
      TcCommit.target s rank = some (oFull L (h / L.block) st) ∧
      rank ∈ X.tcNotified x ∧
      AsyncCopy.WaitObserves X (.async x (.tcNotify rank)) (h, j) (oFull L (h / L.block) st)
        true ws ∧ ScopesMeet L .cluster x.1 ws h

/-- **The routes of a correction access**: a load or store of credit `q ≥ 1` of stage `st` follows
a softmax lane's S-full poll of ordinal `q` in the stage and CTA (rescale), or an earlier
successful poll of the stage's O-full object whose commit follows every PV MMA of the stage of a
tile before `q` (final). -/
def ORoute (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a st : Nat} {vals : List Value}, h < L.threads → 8 ≤ Prologue.warpIndex L h →
    Prologue.warpIndex L h < 12 → (X.TLd (h, i) a vals .s32x32b ∨ X.TSt (h, i) a vals .s32x32b) →
    (∀ j < vals.length, InO st (tcDataCell32 L h a j)) →
    (∃ g e pc p acq sc, g < L.threads ∧ g / L.block = h / L.block ∧ Prologue.warpIndex L g < 8 ∧
      Prologue.warpIndex L g / 4 = st ∧
      X.get (g, e) = some ⟨pc, .wait (sFull L (g / L.block) st) p true acq sc⟩ ∧
      sPolls L X g st e = pArr L X h st i ∧ baseCausality L X (g, e) (h, i)) ∨
    (∃ j pc p acq sc, j < i ∧
      X.get (h, j) = some ⟨pc, .wait (oFull L (h / L.block) st) p true acq sc⟩ ∧
      ∀ x, IsMma X x → (∃ cell, X.MmaCell x cell ∧ InO st cell) →
        x.1 / L.block = h / L.block → pPolls L X x.1 st x.2 ≤ pArr L X h st i →
          oCommits L X x.1 st x.2 ≤ okPolls (oFull L (h / L.block) st) ((X.tr h).take j))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
