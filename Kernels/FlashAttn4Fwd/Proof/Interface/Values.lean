-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Result
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc

@[expose] public section

/-! # What the thread layer exports for the values the softmax and correction compute

With `n = kvBlocks P` key blocks, a softmax thread's score tile `u` (its loads with `u + 1`
successful S-full polls, `sPolls`) is visit `u % n` of its item `u / n`, and a correction thread's
credit `q` (`pArr = q`) lies between the PV MMAs of tiles `q - 1` and `q`: credit `n j + t + 1`
is the rescale of loop trip `t < n - 1` of item `j`, credit `n (j + 1)` its final pass. The
statistics word of a row carries generation `G` of the row's statistics barrier: the softmax
stores generation `(n + 1) j + 1 + t` (the rescale factor of trip `t`) and `(n + 1) j + n` (the
row sum) before its arrival number `G` (`barOrd = G`), and the correction loads it after its
`bar.sync` number `G` (`barOrd = G + 1`, `StatRead`).

The fields state each thread's computation on the values it read, as the role machines'
value tables give them (`Softmax.p0`, `p1`, `alpha`, `lsum0`, `lsum1`; `Correction.rs`, `fw`):

* **softmax** (`SoftValues`): for any scores `S u k` its loads of tile `u` returned
  (`SoftLoads`), there is a reference exponent `c u` and a row sum `l u` per tile such that the
  probabilities it stores are `2 ^ (scale · S u k - c u)` as half-precision values
  (`SoftPStores`, two keys per word, the lower key in the lower half), the row sum is the sum
  of a first tile's probabilities and, in a loop tile, the previous row sum times the rescale
  factor `2 ^ (c (u - 1) - c u)` plus the tile's probabilities, the reference does not decrease
  in a loop tile (the lazy rescale, `Numeric.lazy_rescale`), and the statistics word reads as the
  rescale factor of each loop trip and the row sum of the item's last tile;
* **correction** (`CorrValues`): a rescale store of a cell holds the product of the value its
  load of the cell in the same credit returned and the factor its statistics load of the trip
  read (`rescale`); a trip whose factor is below one rescales every column of the row (`trip`:
  the warp's ballot is then nonzero); and a staging write of the final pass of item `j` holds the
  half-precision product of the final load's value and `1 / l'`, for the row sum `l` its
  statistics load read (`l' = l` unless `l = 0`), at the row of the thread (`final`).

Each computed value is an exact real (assumptions `fa4-fwd-ideal-arith`, `fa4-fwd-approx-exp2-rcp`
and `fa4-fwd-sw-exp2`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The softmax thread `h` of stage `st` and of the row of thread `g`, in `g`'s CTA. -/
def SoftPartner (L : Launch) (g st h : Nat) : Prop :=
  h < L.threads ∧ warpOf L h < 8 ∧ warpOf L h / 4 = st ∧ ctaOf L h = ctaOf L g ∧
    rowOf L h = rowOf L g

/-- The key of register `p` of a probability store to address `a` by softmax thread `h`: its
word holds keys `2 c` and `2 c + 1` of column `c` of the stage's probabilities. -/
def pKey (L : Launch) (h a p : Nat) : Nat :=
  2 * ((tcDataCell32 L h a p).column - (128 * (warpOf L h / 4) + 64))

/-- Softmax thread `h`'s loads of tile `u` returned the scores `S u k` of their columns `k`. -/
def SoftLoads (L : Launch) (X : Execution) (h : Nat) (S : Nat → Nat → ℝ) : Prop :=
  ∀ {i a p u : Nat} {vals : List Value}, X.TLd (h, i) a vals .s32x32b →
    sPolls L X h (warpOf L h / 4) i = u + 1 → p < vals.length →
      vals[p]? = some (.float .f32 (S u ((tcDataCell32 L h a p).column - 128 * (warpOf L h / 4))))

/-- Softmax thread `h`'s stores of tile `u` write the probabilities `pv u k` as half-precision
values, two keys per word. -/
def SoftPStores (L : Launch) (X : Execution) (h : Nat) (pv : Nat → Nat → ℝ) : Prop :=
  ∀ {i a p u : Nat} {vals : List Value}, X.TSt (h, i) a vals .s32x32b →
    sPolls L X h (warpOf L h / 4) i = u + 1 → p < vals.length →
      vals[p]? = some (.pair (.float .f16 (pv u (pKey L h a p)))
        (.float .f16 (pv u (pKey L h a p + 1))))

/-- **The softmax values** of thread `h` for the scores `S` of its loads: per tile `u`, the
reference exponent `c u` and the row sum `l u`. -/
structure SoftValues (P : Params) (L : Launch) (X : Execution) (h : Nat) (S : Nat → Nat → ℝ)
    (c l : Nat → ℝ) : Prop where
  /-- The stored probabilities are `2 ^ (scale · S u k - c u)`. -/
  pStore : SoftPStores L X h fun u k => (2 : ℝ) ^ (P.scale * S u k - c u)
  /-- The row sum of the first tile of an item. -/
  sumFirst : ∀ u, u % kvBlocks P = 0 →
    l u = ∑ k ∈ Finset.range 128, (2 : ℝ) ^ (P.scale * S u k - c u)
  /-- The reference does not decrease in a loop tile. -/
  refStep : ∀ u, u % kvBlocks P ≠ 0 → c (u - 1) ≤ c u
  /-- The row sum of a loop tile. -/
  sumStep : ∀ u, u % kvBlocks P ≠ 0 →
    l u = l (u - 1) * 2 ^ (c (u - 1) - c u) +
      ∑ k ∈ Finset.range 128, (2 : ℝ) ^ (P.scale * S u k - c u)
  /-- The statistics word of generation `(n + 1) j + 1 + t` reads as the rescale factor of loop
  trip `t` of item `j`. -/
  alphaStore : ∀ {i pc j t : Nat} {a : Acc} {ws : List Byte},
    X.get (h, i) = some ⟨pc, .wr a ws⟩ → SoftStore L X h i a true → t + 1 < kvBlocks P →
    barOrd X h i (warpOf L h + 3) = (kvBlocks P + 1) * j + 1 + t →
      F32Word ws ((2 : ℝ) ^ (c (kvBlocks P * j + t) - c (kvBlocks P * j + t + 1)))
  /-- The statistics word of generation `(n + 1) j + n` reads as the row sum of item `j`'s last
  tile. -/
  sumStore : ∀ {i pc j : Nat} {a : Acc} {ws : List Byte},
    X.get (h, i) = some ⟨pc, .wr a ws⟩ → SoftStore L X h i a true →
    barOrd X h i (warpOf L h + 3) = (kvBlocks P + 1) * j + kvBlocks P →
      F32Word ws (l (kvBlocks P * j + kvBlocks P - 1))

/-- Correction thread `g`'s load `r` of its statistics word of stage `st` after its `bar.sync`
number `G` on the stage's statistics barrier, returning `bs`. -/
def StatRead (L : Launch) (X : Execution) (g st G r : Nat) (bs : List (Option Byte)) : Prop :=
  ∃ pc a, X.get (g, r) = some ⟨pc, .rd a bs⟩ ∧ CorrLoad L X g r a false st ∧
    barOrd X g r (warpOf L g - 5 + 4 * st) = G + 1

/-- Correction thread `g` stored `y` in credit `u` at column `d` of its row of stage `st`'s
accumulator. -/
def CorrStored (L : Launch) (X : Execution) (g st u d : Nat) (y : ℝ) : Prop :=
  ∃ i a p, ∃ vals : List Value, X.TSt (g, i) a vals .s32x32b ∧ pArr L X g st i = u ∧
    p < vals.length ∧
    (tcDataCell32 L g a p).column = 256 + 128 * st + d ∧ vals[p]? = some (.float .f32 y)

/-- **The correction values** of thread `g`. -/
structure CorrValues (P : Params) (L : Launch) (X : Execution) (g : Nat) : Prop where
  /-- A rescale store of credit `q` holds, at each cell, the product of the value the load of
  the cell in credit `q` returned and the factor the statistics load of the trip read. -/
  rescale : ∀ {i a p st q : Nat} {vals : List Value}, X.TSt (g, i) a vals .s32x32b → st < 2 →
    pArr L X g st i = q → p < vals.length → InO st (tcDataCell32 L g a p) →
      ∃ i' a' p' r, ∃ vals' : List Value, ∃ bs : List (Option Byte), i' < i ∧
        X.TLd (g, i') a' vals' .s32x32b ∧ pArr L X g st i' = q ∧ p' < vals'.length ∧
        tcDataCell32 L g a' p' = tcDataCell32 L g a p ∧ r < i ∧
        StatRead L X g st ((kvBlocks P + 1) * ((q - 1) / kvBlocks P) + 1 +
          (q - 1) % kvBlocks P) r bs ∧
        (F32s vals' → ∀ o α : ℝ, vals'[p']? = some (.float .f32 o) →
          F32Read bs α → vals[p]? = some (.float .f32 (o * α)))
  /-- Past loop trip `t` of item `j` (its credit arrival), the thread read the trip's factor;
  when it is below one, the thread rescaled every column of its row. -/
  trip : ∀ {st j t e : Nat}, st < 2 → t + 1 < kvBlocks P →
    kvBlocks P * j + t + 2 ≤ pArr L X g st e →
      ∃ r, ∃ bs : List (Option Byte), r < e ∧
        StatRead L X g st ((kvBlocks P + 1) * j + 1 + t) r bs ∧
        ∀ α : ℝ, F32Read bs α → α < 1 →
          (∀ k < e, ∀ pc a' (vals' : List Value),
            X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') →
          (∀ k < e, ∀ pc (ac : Acc) (bs' : List (Option Byte)),
            X.get (g, k) = some ⟨pc, .rd ac bs'⟩ → ∃ x, F32Read bs' x) →
          ∀ d < 128, ∃ y, CorrStored L X g st (kvBlocks P * j + t + 1) d y
  /-- A write of the staging byte of slot `(x, y, k)` of half `hh` of stage `st` is at the
  thread's row, after the final load of the slot's column in the final credit of the item
  (numbered by the staged arrivals) and the load of the row sum; it writes byte `k` of the
  half-precision product of the loaded value and `1 / l'`. -/
  final : ∀ {n st hh x y k : Nat} {dst : Acc} {bs : List Byte}, X.Writes (g, n) dst bs →
    st < 2 → hh < 2 → x < 64 → y < 128 → k < 2 → dst.Covers (stageLoc L (ctaOf L g) st hh x y k) →
      y = rowOf L g ∧ ∃ i a p r, ∃ vals : List Value, ∃ bl : List (Option Byte), i < n ∧
        X.TLd (g, i) a vals .s32x32b ∧
        pArr L X g st i =
          kvBlocks P * (arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take n) + 1) ∧
        p < vals.length ∧ (tcDataCell32 L g a p).column = 256 + 128 * st + (64 * hh + x) ∧
        StatRead L X g st ((kvBlocks P + 1) * arrivals (stagedBar L (ctaOf L g) st)
          ((X.tr g).take n) + kvBlocks P) r bl ∧
        (F32s vals → ∀ o l : ℝ, vals[p]? = some (.float .f32 o) → F32Read bl l →
          wbyte dst bs (stageLoc L (ctaOf L g) st hh x y k) =
            some ((Value.float .f16 (o * (1 / if l = 0 then 1 else l))).byteAt k))

/-- The thread layer's facts for the values the softmax and correction compute. -/
structure ValueFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- Every softmax thread computes on the scores it loaded. -/
  soft : ∀ {h : Nat} {S : Nat → Nat → ℝ}, h < L.threads → warpOf L h < 8 → SoftLoads L X h S →
    ∃ c l, SoftValues P L X h S c l
  /-- Every correction thread computes on the values it loaded. -/
  corr : ∀ {g : Nat}, g < L.threads → 8 ≤ warpOf L g → warpOf L g < 12 → CorrValues P L X g

end
end PTX.Kernels.FlashAttn4Fwd.Proof
