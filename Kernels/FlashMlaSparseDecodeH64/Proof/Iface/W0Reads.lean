-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
-- iface: W0Rows producer=N status=stated domain=consistent
-- iface: ScoreRead producer=N status=stated domain=valid-rows
-- iface: MaskRead producer=N status=stated domain=valid-rows
-- iface: OutRead producer=N status=stated domain=valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi

@[expose] public section

/-! # Warpgroup 0's loads "read as" the reference's numbers

Two links between the words a lane of warpgroup 0 read in its finished blocks and the Spec's
reference, each stated at the lane's row-sum read of the epilogue (pc 1157), where the lane's
finished blocks are all of its CTA's blocks (`w0Fin` of the prefix). A lane `g` is row
`(e, q, h)` = (`%ctaid.y`, `%ctaid.x`, `%tid.x % 64`), half `%tid.x / 64` (the half selects
columns `32 half + i` of each 64-column block).

* `ScoreRead`: the lane's score words of block `t` read as the QK product of Q and the dequantized
  K of the block's slot: where the mask keeps column `i`, the high score word plus the peer's word
  is `score`.
* `MaskRead`: the validity word's bit `i` is `slotValid` of the block's slot.

* `OutRead`: at a staging store of the output (pcs `ost2Base c + j`), the lane's accumulator words
  are 64, the sink word reads as the sink's exponent (`-inf` without a sink), and word `i` reads as
  the number `O` with `O 2 ^ m` the sum over the finished blocks and their 64 slots of weight times
  value of the output column `128 half + off c + i` (`m` the carried maximum).

"Valid rows": all three take `W0Rows`, the words of the lanes' blocks being finite numbers.
Both are stated, not proved: the word-level reads of the Tensor Memory loads and the index
lanes' values are another lane's. The block's cache tag and slot are those of the reference
(`blockExtra`, `blockSlot` of `Lib/Result/Run.lean`), written here in the Spec's terms. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- The batch (`%ctaid.y`) of lane `g`. -/
def w0Batch (L : Launch) (g : Nat) : Nat := (L.ctaidOf (g / L.block)).y % 2 ^ 32

/-- The query (`%ctaid.x`) of lane `g`. -/
def w0Query (L : Launch) (g : Nat) : Nat := (L.ctaidOf (g / L.block)).x % 2 ^ 32

/-- The head of lane `g` (`%tid.x % 64`). -/
def w0Head (L : Launch) (g : Nat) : Nat := (L.tidOf g).x % 64

/-- The half of lane `g` (`%tid.x / 64`): its columns of a block are `32 half + i`. -/
def w0Half (L : Launch) (g : Nat) : Nat := (L.tidOf g).x / 64

/-- The main cache's block count of batch `e` (`orig_topk_padded / 64`, at least one). -/
def w0OrigBlocks (P : Params) (e : Nat) : Nat := max ((P.topkLen e + 63) / 64) 1

/-- The cache tag of block `t` of batch `e`: the extra cache after the main cache's blocks. -/
def w0BlockExtra (P : Params) (e t : Nat) : Bool := decide (w0OrigBlocks P e ≤ t)

/-- The position of column `j` of block `t` in its cache's index array. -/
def w0BlockSlot (P : Params) (e t j : Nat) : Nat :=
  if w0BlockExtra P e t then (t - w0OrigBlocks P e) * 64 + j else t * 64 + j

/-- **The valid rows**: the words of every lane of warpgroup 0 (`%tid.x < 128`) are valid
(`W0Trace`: finite numbers at the end of every prefix). The guard of `ScoreRead` and
`MaskRead`. -/
def W0Rows (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g, g < L.threads → (L.tidOf g).x < 128 → W0Trace P X g

/-- **The scores a lane read** (valid rows): at the lane's epilogue, every finished block `t`
keeps the column `i` that its mask word keeps, and there the high score word plus the peer's word
reads as the QK product `score` of the block's slot. -/
def ScoreRead (P : Params) (L : Launch) (X : Execution) (_hvalid : W0Rows P L X) : Prop :=
  ∀ g k e, g < L.threads → X.get (g, k) = some e → e.pc = 1157 →
    ∀ t seg, (w0Fin ((X.tr g).take k)).1[t]? = some seg → ∀ i < 32, w0Bit (w0Words seg).mw i →
      w0F ((w0Words seg).hi.getD i (.pred false)) + w0PeerF (w0Words seg) i =
        score P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) t)
          (w0BlockSlot P (w0Batch L g) t (32 * w0Half L g + i))

/-- **The masks a lane read** (valid rows): bit `i` of the mask word of every finished block `t`
is `slotValid` of the block's slot `32 half + i`. -/
def MaskRead (P : Params) (L : Launch) (X : Execution) (_hvalid : W0Rows P L X) : Prop :=
  ∀ g k e, g < L.threads → X.get (g, k) = some e → e.pc = 1157 →
    ∀ t seg, (w0Fin ((X.tr g).take k)).1[t]? = some seg → ∀ i < 32,
      (w0Bit (w0Words seg).mw i = true ↔
        slotValid P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) t)
          (w0BlockSlot P (w0Batch L g) t (32 * w0Half L g + i)))

/-- The sink word the reference gives head `h`: `s * sinkLog2Factor`, `-inf` for none. -/
def w0SinkE (P : Params) (h : Nat) : EReal :=
  match P.sink h with
  | some s => ((s * sinkLog2Factor : ℝ) : EReal)
  | none => ⊥

/-- **The output a lane staged** (valid rows): at every staging store `ost2 c j` of a lane, its
accumulator words (the last chunk load) are 64, the sink word reads as `w0SinkE`, and word `i`
reads as a number `O` with `O 2 ^ m` the sum over the finished blocks `t` and their 64 slots `j'`
of `weight * value` of the output column `128 half + [0, 64, 256, 320][c] + i`, where `m` is the
maximum the finished blocks carry. -/
def OutRead (P : Params) (L : Launch) (X : Execution) (_hvalid : W0Rows P L X) : Prop :=
  ∀ g k e (c : Fin 4) (j : Fin 8), g < L.threads → X.get (g, k) = some e →
    e.pc = Wg0.ost2Base c + j.val →
    (w0EpiO (w0Scan ((X.tr g).take k)).2).length = 64 ∧
    Rd (w0SkWord ((X.tr g).take k)) (w0SinkE P (w0Head L g)) ∧
    ∀ i < 64, ∃ O : ℝ,
      Rd ((w0EpiO (w0Scan ((X.tr g).take k)).2).getD i (.pred false)) (O : EReal) ∧
      O * (2 : ℝ) ^ (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 =
        ∑ t ∈ Finset.range (w0Fin ((X.tr g).take k)).1.length, ∑ j' ∈ Finset.range 64,
          weight P (w0Batch L g) (w0Query L g) (w0Head L g) (w0BlockExtra P (w0Batch L g) t)
              (w0BlockSlot P (w0Batch L g) t j') *
            slotValue P (w0Batch L g) (w0Query L g) (w0BlockExtra P (w0Batch L g) t)
              (w0BlockSlot P (w0Batch L g) t j')
              (128 * w0Half L g + [0, 64, 256, 320].getD c.val 0 + i)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
