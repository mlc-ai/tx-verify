-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
public import Core.Tc.TmemStore
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemAccess

@[expose] public section

/-! # The Tensor Memory facts the protocols read

`ScoreFacts` (the scores and probabilities) and `OAccFacts` (the output accumulator): one lane of a
CTA's warp 12 issues its MMAs and commits; the QK and PV MMAs, the softmax loads and P stores and
the correction loads and stores with the counts that number their uses. They are event-level facts
of single lanes, proved from the role exports in `Protocol/Tmem/FactsProof.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- An MMA issue. -/
abbrev IsMma (X : Execution) (i : EvId) : Prop := Tmem1.IsMma X i

/-- The facts for the score hand-off and the P-full objects. -/
structure ScoreFacts (L : Launch) (X : Execution) : Prop where
  /-- The kernel has no `tcgen05.cp`. -/
  no_cp : ∀ e c, ¬ X.CpIssue e c
  /-- The kernel has no `tcgen05.shift`. -/
  no_shift : ∀ e s, ¬ X.ShiftIssue e s
  /-- An MMA is issued by warp 12; its result cells are all in one stage's scores or all in one
  stage's output accumulator, in the issuer's CTA. -/
  mma_cells : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → i.1 < L.threads ∧ Prologue.warpIndex L i.1 = 12 ∧ ∃ st < 2,
        (∀ cell, X.MmaCell i cell → InS st cell ∧ cell.cta = i.1 / L.block) ∨
          (∀ cell, X.MmaCell i cell → InO st cell ∧ cell.cta = i.1 / L.block)
  /-- One lane of a CTA issues its MMAs and makes its commits. -/
  tc_one : ∀ {i i' : EvId}, IsMma X i →
    (IsMma X i' ∨ ∃ s, X.Commit i' s) →
    i.1 / L.block = i'.1 / L.block → i.1 = i'.1
  /-- MMAs writing one stage's scores, or one stage's accumulator, of one CTA use the same
  accumulator. -/
  mma_acc : ∀ {i i' : EvId} {d d' st : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} {cell cell' : Cell}, X.MmaIssue i d s acc mask →
    X.MmaIssue i' d' s' acc' mask' → X.MmaCell i cell → X.MmaCell i' cell' →
    cell.cta = cell'.cta → st < 2 →
    (InS st cell ∧ InS st cell') ∨ (InO st cell ∧ InO st cell') → SameAccumulator d s d' s'
  /-- A QK MMA of score tile `u` follows the MMA lane's polls of phases `0 … u - 1` of both P-full
  objects. -/
  qk_polls : ∀ {i : EvId} {cell : Cell} {st : Nat}, st < 2 → IsMma X i → X.MmaCell i cell → InS st
      cell →
    sCommits L X i.1 st i.2 ≤ pPolls L X i.1 st i.2 ∧
      sCommits L X i.1 st i.2 ≤ p2Polls L X i.1 st i.2
  /-- A PV MMA of tile `u` (`pPolls = u + 1`) reads its A operand from Tensor Memory, in its
  stage's probabilities, and when it reads columns `112 …` it follows the poll of phase `u` of the
  second object; it comes after the commit of score tile `u` and before that of `u + 1`. -/
  pv_polls : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {cell : Cell} {st : Nat}, X.MmaIssue i d s acc mask → X.MmaCell i cell → InO st cell →
    1 ≤ pPolls L X i.1 st i.2 ∧ sCommits L X i.1 st i.2 ≤ pPolls L X i.1 st i.2 ∧
      s.aTmem.isSome ∧ ∀ index c pos, aCell s index = some (c, pos) →
        InP st c ∧ c.cta = i.1 / L.block ∧
          (InPHigh st c → p2Polls L X i.1 st i.2 = pPolls L X i.1 st i.2)
  /-- The PV MMAs of tile `u` come before the QK MMAs of later score tiles. -/
  pv_qk : ∀ {i i' : EvId} {cell cell' : Cell} {st : Nat}, st < 2 → IsMma X i →
    IsMma X i' → i.1 = i'.1 → X.MmaCell i cell → InO st cell → X.MmaCell i' cell' → InS st cell' →
    pPolls L X i.1 st i.2 ≤ sCommits L X i'.1 st i'.2 → i.2 < i'.2
  /-- An MMA's lane masks are zero: each of its result cells is written. -/
  mma_reads : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {row col : Nat} {cell : Cell}, X.MmaIssue i d s acc mask →
    resultCell s d row col = some cell → X.MmaCell i cell
  /-- Every MMA writes a cell. -/
  mma_cell : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → ∃ cell, X.MmaCell i cell
  /-- A QK MMA reads its A operand from shared memory. -/
  qk_smem : ∀ {i : EvId} {d st : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {cell : Cell}, st < 2 → X.MmaIssue i d s acc mask → X.MmaCell i cell → InS st cell →
      s.aTmem = none
  /-- Tensor Memory loads and stores are made by softmax and correction lanes. -/
  tc_role : ∀ {g i a : Nat} {vals : List Value} {sh : TcShape},
    (X.TLd (g, i) a vals sh ∨ X.TSt (g, i) a vals sh) → g < L.threads ∧ Prologue.warpIndex L g < 12
  /-- Tensor Memory loads and stores have the shape `.32x32b`. -/
  tc_shape : ∀ {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape},
    (X.TLd e a vals sh ∨ X.TSt e a vals sh) → sh = .s32x32b
  /-- A softmax load of tile `u` reads its row of its stage's scores, after `u + 1` polls of the
  S-full object and `u` arrivals on the P-full object; a `wait::ld` comes between it and the
  lane's later arrivals on the object. -/
  soft_ld : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → Prologue.warpIndex L h < 8 →
    X.TLd (h, i) a vals .s32x32b →
      (∀ j < vals.length, InS (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) ∧
      (∀ e ev, i < e → X.get (h, e) = some ev →
        arrivesOn (pFull L (h / L.block) (Prologue.warpIndex L h / 4)) ev = true →
        ∃ w pc, i < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitLd⟩) ∧
      pArr L X h (Prologue.warpIndex L h / 4) i + 1 = sPolls L X h (Prologue.warpIndex L h / 4) i
  /-- A softmax store of tile `u` writes its row of its stage's probabilities, either all below
  or all from column `112`, for the columns below `112` before the tile's arrival on the P-full
  object; every later event of the lane that is not a `tcgen05` event comes after a `wait::st` of
  the tile that follows the store. -/
  soft_st : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → Prologue.warpIndex L h < 8 →
    X.TSt (h, i) a vals .s32x32b →
      (∀ j < vals.length, InP (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) ∧
      ((∀ j < vals.length, ¬ InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) ∨
        ∀ j < vals.length, InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) ∧
      1 ≤ sPolls L X h (Prologue.warpIndex L h / 4) i ∧
      ((∀ j < vals.length, InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j)) ∨
        pArr L X h (Prologue.warpIndex L h / 4) i + 1 = sPolls L X h (Prologue.warpIndex L h / 4)
            i) ∧
      ∀ e, NonTcAfter X h i e →
      ∃ w pc, i < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
        sPolls L X h (Prologue.warpIndex L h / 4) w = sPolls L X h (Prologue.warpIndex L h / 4) i
  /-- A softmax lane's arrival on the P-full object follows one S-full poll more than its earlier
  arrivals. -/
  soft_p : ∀ {h i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope}, Prologue.warpIndex L h < 8 →
    X.get (h, i) = some ⟨pc,
      .arrive (pFull L (h / L.block) (Prologue.warpIndex L h / 4)) tx cnt rel sc⟩ →
    pArr L X h (Prologue.warpIndex L h / 4) i + 1 = sPolls L X h (Prologue.warpIndex L h / 4) i
  /-- A softmax lane's loads of a tile come before its stores of the tile. -/
  soft_ld_st : ∀ {h i i' a a' : Nat} {vals vals' : List Value}, h < L.threads →
    Prologue.warpIndex L h < 8 → X.TLd (h, i) a vals .s32x32b → X.TSt (h, i') a' vals' .s32x32b →
    sPolls L X h (Prologue.warpIndex L h / 4) i = sPolls L X h (Prologue.warpIndex L h / 4) i' → i
        < i'
  /-- A softmax lane stores each cell once per tile. -/
  soft_st_one : ∀ {h i i' a a' j j' : Nat} {vals vals' : List Value}, h < L.threads →
    Prologue.warpIndex L h < 8 → X.TSt (h, i) a vals .s32x32b → X.TSt (h, i') a' vals' .s32x32b →
    j < vals.length →
    j' < vals'.length → tcDataCell32 L h a j = tcDataCell32 L h a' j' →
    sPolls L X h (Prologue.warpIndex L h / 4) i = sPolls L X h (Prologue.warpIndex L h / 4) i' → i
        = i'

namespace ScoreFacts

variable {L : Launch} {X : Execution}

/-- A load's cell, with the load's shape `.32x32b`. -/
theorem loadCell (ht : ScoreFacts L X) {load : EvId} {j : Nat} {cell : Cell}
    (h : LoadCell L X load j cell) :
    ∃ a vals, X.TLd load a vals .s32x32b ∧ j < vals.length ∧ cell = tcDataCell32 L load.1 a j := by
  obtain ⟨a, vals, sh, hl, hj, rfl⟩ := h
  obtain rfl := ht.tc_shape (.inl hl)
  exact ⟨a, vals, hl, hj, tcDataCell_s32x32b _ _ _ _⟩

/-- A store's cell, with the store's shape `.32x32b`. -/
theorem storeCell (ht : ScoreFacts L X) {st : EvId} {cell : Cell} (h : StoreCell L X st cell) :
    ∃ a vals j, X.TSt st a vals .s32x32b ∧ j < vals.length ∧ cell = tcDataCell32 L st.1 a j := by
  obtain ⟨a, vals, sh, j, hs, hj, rfl⟩ := h
  obtain rfl := ht.tc_shape (.inr hs)
  exact ⟨a, vals, j, hs, hj, tcDataCell_s32x32b _ _ _ _⟩

end ScoreFacts

/-- A `.32x32b` store's cell. -/
theorem storeCell32 {L : Launch} {X : Execution} {e : EvId} {a j : Nat} {vals : List Value}
    (h : X.TSt e a vals .s32x32b) (hj : j < vals.length) :
    StoreCell L X e (tcDataCell32 L e.1 a j) :=
  ⟨a, vals, .s32x32b, j, h, hj, (tcDataCell_s32x32b _ _ _ _).symm⟩

/-- The facts for the output accumulator. -/
structure OAccFacts (L : Launch) (X : Execution) : Prop where
  /-- A correction load of credit `q ≥ 1` reads its row of one stage's accumulator; its `wait::ld`
  is the lane's next event, if it has one. -/
  corr_ld : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ Prologue.warpIndex L h →
    Prologue.warpIndex L h < 12 → X.TLd (h, i) a vals .s32x32b → ∃ st < 2,
      (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧
      (∀ e, NonTcAfter X h i e → ∃ pc, X.get (h, i + 1) = some ⟨pc, .tc .waitLd⟩) ∧
      1 ≤ pArr L X h st i
  /-- A correction store of credit `q ≥ 1` writes its row of one stage's accumulator; every later
  event of the lane that is not a `tcgen05` event comes after a `wait::st` of the same credit that
  follows the store. -/
  corr_st : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ Prologue.warpIndex L h →
    Prologue.warpIndex L h < 12 → X.TSt (h, i) a vals .s32x32b → ∃ st < 2,
      (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧ 1 ≤ pArr L X h st i ∧
      ∀ e, NonTcAfter X h i e →
        ∃ w pc, i < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
          pArr L X h st w = pArr L X h st i
  /-- A correction load of a cell comes before the store of the cell of the same credit. -/
  corr_ld_st : ∀ {h i i' a a' j j' st : Nat} {vals vals' : List Value}, h < L.threads →
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 → X.TLd (h, i) a vals .s32x32b →
    X.TSt (h, i') a' vals' .s32x32b →
    j < vals.length → j' < vals'.length → tcDataCell32 L h a j = tcDataCell32 L h a' j' →
    InO st (tcDataCell32 L h a j) → pArr L X h st i = pArr L X h st i' → i < i'
  /-- A correction lane stores each cell once per credit. -/
  corr_st_one : ∀ {h i i' a a' j j' st : Nat} {vals vals' : List Value}, h < L.threads →
    8 ≤ Prologue.warpIndex L h → Prologue.warpIndex L h < 12 → X.TSt (h, i) a vals .s32x32b →
    X.TSt (h, i') a' vals' .s32x32b →
    j < vals.length → j' < vals'.length → tcDataCell32 L h a j = tcDataCell32 L h a' j' →
    InO st (tcDataCell32 L h a j) → pArr L X h st i = pArr L X h st i' → i = i'

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
