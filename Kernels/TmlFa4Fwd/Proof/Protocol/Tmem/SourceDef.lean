-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Facts
public import Lemmas.Order.WarpBarOrdinal

@[expose] public section

/-! # The facts for the read sources of the Tensor Memory reads -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- **TmemLive**: an access completes before every release of an allocation that covers its cell. -/
def TmemLive (L : Launch) (X : Execution) : Prop :=
  ∀ {e : EvId} {cell : Cell}, Tmem.Pair.Access L X e cell →
    ∀ cta r, r ∈ X.tmemHistory cta → Tmem.Pair.Covers L X r cell.cta e cell.column →
      ∀ d, Tmem.Pair.ReleaseOf L X r d → TcMma.CompletedBefore L X e d

/-- The facts for the read sources. -/
structure SourceFacts (L : Launch) (X : Execution) : Prop where
  live : TmemLive L X
  /-- A QK MMA of the score tile a softmax load reads writes each cell it loads. -/
  soft_cover : ∀ {h i a j : Nat} {vals : List Value}, h < L.threads →
    Prologue.warpIndex L h < 8 → X.TLd (h, i) a vals .s32x32b → j < vals.length →
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      sCommits L X x.1 (Prologue.warpIndex L h / 4) x.2 + 1 =
        sPolls L X h (Prologue.warpIndex L h / 4) i
  /-- A PV MMA of the tile before a correction load's credit writes each cell it loads. -/
  corr_cover : ∀ {h i a j st : Nat} {vals : List Value}, h < L.threads →
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 → X.TLd (h, i) a vals .s32x32b →
    j < vals.length → InO st (tcDataCell32 L h a j) →
    ∃ x, IsMma X x ∧ X.MmaCell x (tcDataCell32 L h a j) ∧
      pPolls L X x.1 st x.2 = pArr L X h st i
  /-- An accumulating QK MMA follows a QK MMA of its tile writing the cell. -/
  qk_acc : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat},
    st < 2 → X.MmaIssue i d s true mask → X.MmaCell i cell → InS st cell →
    ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ sCommits L X i.1 st k = sCommits L X i.1 st i.2
  /-- An accumulating PV MMA follows a PV MMA of its tile or the tile before writing the cell. -/
  pv_acc : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat},
    X.MmaIssue i d s true mask → X.MmaCell i cell → InO st cell →
    ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ pPolls L X i.1 st i.2 ≤ pPolls L X i.1 st k + 1
  /-- Two MMAs of a lane writing one cell write the same cells. -/
  same_write : ∀ {i i' : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} {cell : Cell}, X.MmaIssue i d s acc mask →
    X.MmaIssue i' d' s' acc' mask' → i.1 = i'.1 → X.MmaCell i cell → X.MmaCell i' cell →
    SameAccumulator d s d' s' ∧ ∀ row col,
      writeCell s d mask row col = writeCell s' d' mask' row col
  /-- A PV MMA's A cells are in the first 128 lanes. -/
  a_lane : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {index pos : Nat} {c : Cell}, X.MmaIssue i d s acc mask → aCell s index = some (c, pos) →
    c.lane < 128
  /-- A softmax lane stores the probabilities below column `112` of its row before its P-full
  arrival of the tile. -/
  soft_low : ∀ {h e pc tx cnt col : Nat} {rel : Bool} {sc : MbarScope},
    Prologue.warpIndex L h < 8 → X.get (h, e) = some ⟨pc,
      .arrive (pFull L (h / L.block) (Prologue.warpIndex L h / 4)) tx cnt rel sc⟩ →
    InP (Prologue.warpIndex L h / 4) (tcDataCell32 L h 0 col) →
    ¬ InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h 0 col) →
    ∃ k a j, ∃ vals : List Value, k < e ∧ X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧
      tcDataCell32 L h a j = tcDataCell32 L h 0 col ∧
      sPolls L X h (Prologue.warpIndex L h / 4) k = pArr L X h (Prologue.warpIndex L h / 4) e + 1
  /-- A softmax lane stores the probabilities from column `112` of its row before its warp barrier
  of the tile. -/
  soft_high : ∀ {h b mask inst col : Nat}, Prologue.warpIndex L h < 8 →
    X.WarpBar (h, b) mask inst → InP (Prologue.warpIndex L h / 4) (tcDataCell32 L h 0 col) →
    InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h 0 col) →
    ∃ k a j, ∃ vals : List Value, k < b ∧ X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧
      tcDataCell32 L h a j = tcDataCell32 L h 0 col ∧
      sPolls L X h (Prologue.warpIndex L h / 4) k = warpBars X h b + 1
  /-- A softmax lane has made its warp barrier of a tile when an MMA of its CTA follows the tile's
  poll of the second P-full barrier of its stage. -/
  elected : ∀ {h u : Nat} {f : EvId}, h < L.threads → Prologue.warpIndex L h < 8 → IsMma X f →
    f.1 / L.block = h / L.block → u + 1 ≤ p2Polls L X f.1 (Prologue.warpIndex L h / 4) f.2 →
    ∃ b mask inst, X.WarpBar (h, b) mask inst ∧ warpBars X h b = u

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
