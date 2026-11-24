-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Facts
public import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # The P-full hand-offs (the statements)

Proved by the P channel; the Tensor Memory orders read them as hypotheses. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- The MMA warp of CTA `c`. -/
def mmaIn (L : Launch) (c g : Nat) : Prop :=
  g < L.threads ∧ g / L.block = c ∧ Prologue.warpIndex L g = 12

/-- A producer of stage `st`'s P-full object of CTA `c`: a softmax lane of the stage or a
correction lane. -/
def pProd (L : Launch) (c st g : Nat) : Prop :=
  g < L.threads ∧ g / L.block = c ∧
    ((Prologue.warpIndex L g < 8 ∧ Prologue.warpIndex L g / 4 = st) ∨
      (8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g < 12))

/-- **PPhase**, the P-full hand-off of every stage of every CTA. -/
def PReadyHandoff (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 → MbarRing.UnitHandoff L X (pFull L c st) (pProd L c st) (mmaIn L c) 0

/-- **The second P-full gate**: a softmax lane's store of tile `u` to columns `112 …` is followed by
a `wait::st` of the tile that happens before every MMA of its CTA after the poll of phase `u` of the
second object. -/
def P2Gate (L : Launch) (X : Execution) : Prop :=
  ∀ {h i a : Nat} {vals : List Value} {f : EvId}, h < L.threads → Prologue.warpIndex L h < 8 →
    X.TSt (h, i) a vals .s32x32b →
    (∀ j < vals.length, InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) →
    IsMma X f → f.1 / L.block = h / L.block →
    sPolls L X h (Prologue.warpIndex L h / 4) i ≤
      p2Polls L X f.1 (Prologue.warpIndex L h / 4) f.2 →
      ∃ w pc, i < w ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧ baseCausality L X (h, w) f

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
