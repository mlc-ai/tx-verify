-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Values

@[expose] public section

/-! # The value links between the roles

The output values (`OutputValues`) follow from the threads' computations (`ValueFacts`) and three
links that say which value a read returns, each the value chain of one handoff:

* **`ScoreLoads`** (the scores): a softmax load of tile `u` returns, at each column `k`, the
  single-precision score `S = Q Kᵀ` of its row with key `visitKey (u % n) k` of its item
  `u / n`. Its chain: the load reads the last QK MMA of tile `u` writing the cell
  (`Score.s_readSource`, `Floats.soft_source`), whose result is the ideal MMA's sum over its
  K steps (`TcMma.Result`, assumption `fa4-fwd-ideal-arith`) of the products of its operand
  elements, the Q half of the item (`QRingSlotSources.read_source`) and the K block of the
  visit (`KvRing`), copied from the inputs `Q` and `K` (`RingCopies.copy`).
* **`StatsReads`** (the statistics word): a correction load after its `bar.sync` number `G`
  returns the bytes the row's softmax thread stored before its arrival number `G`. Its chain is
  the one of `Floats.stats_floats` (`Stats.stats_baseCausality`, the last write of each byte).
* **`PvChain`** (the accumulator): for probabilities `pv u k` the row's softmax thread stores
  in tile `u`, the last PV MMA of tile `u` leaves at column `d` of the correction thread's row
  a value `R u d`: the first tile of an item overwrites with `Σ_k pv u k · V(key, d)`, and a
  loop tile adds that sum to the correction's rescale store of credit `u` at the cell when
  there is one (`OAcc.o_rescale_result`) and to `R (u - 1) d` otherwise
  (`OAcc.o_skip_result`); a correction load of credit `q` returns `R (q - 1) d`
  (`OAcc.o_readSource`, `Floats.corr_source`). Its chain: the MMAs' accumulator sources
  (`TcMmaSources.accSource`), A operands (`TcMmaSources.pvAStore`, Core `AReadOk`) and B
  operands (the V block of the visit, `KvRing`), and the ideal MMA's sum over the eight K steps
  of the tile. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The score of column `k` of tile `u` of softmax thread `h`: query row `tileRow + ρ` of its
stage and key `visitKey (u % n) k` of its item `u / n`. -/
def tileScore (P : Params) (L : Launch) (h u k : Nat) : ℝ :=
  score P (tileBatch L h (u / kvBlocks P)) (tileHead L h (u / kvBlocks P))
    (tileRow L h (u / kvBlocks P) (warpOf L h / 4) + rowOf L h)
    (visitKey P (u % kvBlocks P) k)

/-- **The scores**: every softmax load returns the scores of its tile. -/
def ScoreLoads (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {h : Nat}, h < L.threads → warpOf L h < 8 → SoftLoads L X h (tileScore P L h)

/-- **The statistics word**: a correction load after its `bar.sync` number `G` returns the bytes
of the row's softmax store of generation `G`. -/
def StatsReads (L : Launch) (X : Execution) : Prop :=
  ∀ {g st G r : Nat} {bs : List (Option Byte)}, g < L.threads → 8 ≤ warpOf L g →
    warpOf L g < 12 → st < 2 → StatRead L X g st G r bs →
      ∃ h i pc a, ∃ ws : List Byte, SoftPartner L g st h ∧ X.get (h, i) = some ⟨pc, .wr a ws⟩ ∧
        SoftStore L X h i a true ∧ barOrd X h i (warpOf L h + 3) = G ∧ bs = ws.map some

/-- The value `Σ_k pv u k · V(key, d)` the PV MMAs of tile `u` of correction thread `g`'s item
add at column `d`. -/
def pvSum (P : Params) (L : Launch) (g : Nat) (pv : Nat → Nat → ℝ) (u d : Nat) : ℝ :=
  ∑ k ∈ Finset.range 128, pv u k *
    P.v (tileBatch L g (u / kvBlocks P)) (tileHead L g (u / kvBlocks P))
      (visitKey P (u % kvBlocks P) k) d

/-- **The accumulator**: the values `R u d` the PV MMAs of each tile leave at column `d` of
correction thread `g`'s row of stage `st`, for the probabilities its row's softmax thread
stores. -/
def PvChain (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g st h : Nat} {pv : Nat → Nat → ℝ}, g < L.threads → 8 ≤ warpOf L g → warpOf L g < 12 →
    st < 2 → SoftPartner L g st h → SoftPStores L X h pv →
      ∃ R : Nat → Nat → ℝ,
        (∀ u d, u % kvBlocks P = 0 → d < 128 → R u d = pvSum P L g pv u d) ∧
        (∀ u d y, u % kvBlocks P ≠ 0 → d < 128 → CorrStored L X g st u d y →
          R u d = y + pvSum P L g pv u d) ∧
        (∀ u d, u % kvBlocks P ≠ 0 → d < 128 → (¬ ∃ y, CorrStored L X g st u d y) →
          R u d = R (u - 1) d + pvSum P L g pv u d) ∧
        ∀ {i a p q : Nat} {vals : List Value}, X.TLd (g, i) a vals .s32x32b → pArr L X g st i = q →
          p < vals.length → InO st (tcDataCell32 L g a p) →
            vals[p]? = some (.float .f32
              (R (q - 1) ((tcDataCell32 L g a p).column - (256 + 128 * st))))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
