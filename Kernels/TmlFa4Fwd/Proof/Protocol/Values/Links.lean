-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Real.OnlineFold
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.PvChain
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Score

@[expose] public section

/-! # The links of the value layer

What the value recursion takes from the other layers, for a complete execution: each CTA's tile
(`TileOk`), the blocks its loader warps load (`OperandBytes`, `InputsAre`), the numeric steps of a
softmax lane (`SoftLink`: the probabilities it stores are the row's running softmax of the scores it
loaded) and of a correction lane (`CorrLink`: a rescale store is the loaded accumulator times the
row's factor, and a round without one has a factor of at least one), and the routes of the results
(`OutRoute`, `LseRoute`: an output byte is a byte of a final load over the row sum, and a
log-sum-exp store is the row's). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Numeric.OnlineFold
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

/-- **The tile of a CTA**: its request, its head, its first row and its number of K/V blocks. -/
structure Tile where
  batch : Nat
  head : Nat
  row : Nat
  n : Nat

/-- The key of column `k` of the block of tile round `u`: the blocks are visited from the last. -/
def Tile.key (t : Tile) (u k : Nat) : Nat := 128 * (t.n - 1 - u) + k

/-- A request row of a tile. -/
def Tile.rowOf (t : Tile) (st ρ : Nat) : Nat := t.row + 128 * st + ρ

/-- A valid row of a tile. -/
def Tile.Valid (p : Params) (t : Tile) (st ρ : Nat) : Prop := t.rowOf st ρ < p.qLength t.batch

/-- **The tile's request, head and blocks are in range**, and the blocks hold the rows' keys. -/
structure TileOk (p : Params) (t : Tile) : Prop where
  batch : t.batch < p.batch
  head : t.head < p.heads
  blocks : 0 < t.n
  keys : ∀ st < 2, ∀ ρ < 128, t.Valid p st ρ →
    p.keyCount t.batch (t.rowOf st ρ) ≤ 128 * t.n

/-- **The loaded blocks are the tile's inputs**, at the tile's valid rows and the request's keys. -/
structure InputsAre (p : Params) (t : Tile) (I : Inputs) : Prop where
  q : ∀ st < 2, ∀ ρ < 128, t.Valid p st ρ → ∀ d < 128,
    I.q st ρ d = p.q (p.qOffset t.batch + t.rowOf st ρ) t.head d
  k : ∀ u < t.n, ∀ k < 128, t.key u k < p.kLength t.batch → ∀ d < 128,
    I.k u k d = p.k (p.page t.batch (t.key u k / 16)) (t.head / 6) (t.key u k % 16) d
  v : ∀ u < t.n, ∀ k < 128, t.key u k < p.kLength t.batch → ∀ d < 128,
    I.v u k d = p.v (p.page t.batch (t.key u k / 16)) (t.head / 6) (t.key u k % 16) d

/-- The bias of a row's key, zero outside the packed columns. -/
def biasAt (p : Params) (b h row j : Nat) : ℝ :=
  if 0 ≤ p.biasColumn b row j ∧ p.biasColumn b row j < 1280 then
    (p.bias (p.qOffset b + row) h (p.biasColumn b row j).toNat).getD 0 else 0

/-- **The weight of a column of a tile round**, from the score `s` the row's lane loaded: zero for a
key the row does not attend. -/
def weightOf (p : Params) (t : Tile) (row : Nat) (S : Nat → Nat → ℝ) (u k : Nat) : ℝ :=
  if t.key u k < p.keyCount t.batch row then
    (2 : ℝ) ^ (abiFloat p.scaleLog2Bits * (S u k + abiFloat p.invScaleBits *
      biasAt p t.batch t.head row (t.key u k))) else 0

/-- **What a softmax lane computes**: the probabilities it stores, the scales and the factors of its
rounds, its final row sum and row maximum. -/
structure RowData where
  P : Nat → Nat → ℝ
  c : Nat → ℝ
  f : Nat → ℝ
  rs : ℝ
  rm : ℝ

/-- The row of a lane in its stage. -/
abbrev rowIx (L : Launch) (g : Nat) : Nat := g % L.block % 128

/-- **The numeric steps of the softmax lanes**: once a lane's loads return scores `S`, the words it
stores are the probabilities of its row, and at a valid row these are the running softmax of the
weights of `S`, its last scale being the one of its row maximum. -/
def SoftLink (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop :=
  ∀ h < L.threads, Prologue.warpIndex L h < 8 → ∀ S : Nat → Nat → ℝ,
    (∀ {i a j u : Nat} {vals : List Value}, X.TLd (h, i) a vals .s32x32b → j < vals.length →
      sPolls L X h (Prologue.warpIndex L h / 4) i = u + 1 →
      vals[j]? = some (.float .f32 (S u
        ((tcDataCell32 L h a j).column - 128 * (Prologue.warpIndex L h / 4))))) →
    PStored L X h (D h).P ∧ ∀ t, T (h / L.block) = some t →
      t.Valid p (Prologue.warpIndex L h / 4) (rowIx L h) →
        Fold t.n (weightOf p t (t.rowOf (Prologue.warpIndex L h / 4) (rowIx L h)) S) (D h).P
          (D h).c (D h).f (D h).rs ∧
        (D h).c (t.n - 1) = (2 : ℝ) ^ (-(abiFloat p.scaleLog2Bits * (D h).rm))

/-- **The rescale rounds of the correction lanes**: a store of credit `u` is the loaded accumulator
of that credit times the row's factor of round `u`, and a round without a store of a cell has a
factor of at least one. -/
structure CorrLink (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop where
  store : ∀ {g k a j st u : Nat} {vals : List Value}, st < 2 → 8 ≤ Prologue.warpIndex L g →
    Prologue.warpIndex L g < 12 → X.TSt (g, k) a vals .s32x32b → j < vals.length →
    InO st (tcDataCell32 L g a j) → pArr L X g st k = u →
    ∃ k' a' j' x, ∃ vals' : List Value, X.TLd (g, k') a' vals' .s32x32b ∧ j' < vals'.length ∧
      tcDataCell32 L g a' j' = tcDataCell32 L g a j ∧ pArr L X g st k' = u ∧
      vals'[j']? = some (.float .f32 x) ∧
      vals[j]? = some (.float .f32 (x * (D (softLane L (g / L.block) st (rowIx L g))).f u))
  skip : ∀ {c t st ρ d u : Nat}, ∀ tl, T c = some tl → t = tl.n → c < L.grid → st < 2 → ρ < 128 →
    d < 128 → tl.Valid p st ρ → 1 ≤ u → u < t →
    (¬ ∃ y, CorrStored L X st ⟨c, ρ, 256 + 128 * st + d⟩ u y) →
      1 ≤ (D (softLane L c st ρ)).f u

/-- **The links of the value recursion** of a complete execution. -/
structure ValueLinks (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (I : Nat → Inputs) (D : Nat → RowData) : Prop where
  tile : ∀ c t, T c = some t → c < L.grid ∧ TileOk p t
  bytes : OperandBytes I L X
  inputs : ∀ c t, T c = some t → InputsAre p t (I c)
  soft : SoftLink p L X T D
  corr : CorrLink p L X T D

/-- **The route of the output bytes**: a byte of an output element of a valid row is that of a final
load of the row's correction lane, of the credit after the last tile, over the row sum. -/
def OutRoute (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop :=
  ∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b, ∀ d < 128, ∀ k < 4, ∀ w a bytes,
    X.MemWrites w a bytes → a.Covers ((p.oLoc (p.qOffset b + row) h d).at k) →
    ∃ t st g i ad j x, ∃ vals : List Value, T (g / L.block) = some t ∧ t.batch = b ∧ t.head = h ∧
      st < 2 ∧ 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g < 12 ∧
      row = t.rowOf st (rowIx L g) ∧ X.TLd (g, i) ad vals .s32x32b ∧ j < vals.length ∧
      (tcDataCell32 L g ad j).column = 256 + 128 * st + d ∧ pArr L X g st i = t.n ∧
      vals[j]? = some (.float .f32 x) ∧
      wbyte a bytes ((p.oLoc (p.qOffset b + row) h d).at k) = some ((Value.float .f32
        (x * (D (softLane L (g / L.block) st (rowIx L g))).rs⁻¹)).byteAt k)

/-- **The route of the log-sum-exp stores**: a global store of a lane is the row's log-sum-exp, from
the row's sum and maximum, at the row's word. -/
def LseRoute (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop :=
  ∀ i a bytes, X.Writes i a bytes → a.loc.space = .global →
    ∃ c t st ρ, T c = some t ∧ st < 2 ∧ ρ < 128 ∧ t.Valid p st ρ ∧
      a.loc = p.lseLoc (p.qOffset t.batch + t.rowOf st ρ) t.head ∧ a.size = 4 ∧
      bytes = (Value.float .f32 ((abiFloat p.scaleLog2Bits * (D (softLane L c st ρ)).rm +
        Real.logb 2 (D (softLane L c st ρ)).rs) * abiFloat 0x3F317218)).toBytes

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
