-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlockFull

@[expose] public section

/-! # The value of a block of the data machine

`w0_block`: a block `b` of the data machine that holds the words `w` of a valid block
(`BlkIs`, which the trace invariant `InvW` gives) and the statistics it starts from, read as
numbers, has at its last link the new maximum, the new running sum and the bf16 words of the
probabilities of `w0Next`. -/

/-! # The value of one block

From the words of a valid block (`W0Ok`) and the statistics it starts from (`m`, `l`, `mx`, read
as numbers), the facts at the probability stores (`f_ost`) hold the new maximum (`w0Max`), the new
running sum (`w0Next`) and the sixteen bf16 probabilities. The proof is `w0_block_full`'s. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

/-- The statistics a block starts from, read as numbers, and the value the block gives. -/
theorem w0_block_vars {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {x : BitVec 64}
    (hx : Rd (.bits 32 x) (sc : EReal)) {m l mx sk : Value} {lo : List Value} {mR lR : ℝ}
    (hm : Rd m (mR : EReal)) (hl : Rd l (lR : EReal)) {r0 : EReal} (hmx : Rd mx r0) :
    let V := lookupD (f_ost x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
      (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt)
    Rd (V 2950) ((w0Max sc mR w : ℝ) : EReal) ∧
      Rd (V 2955) (((w0Next sc (mR, lR) w).2 : ℝ) : EReal) ∧
      (∀ t < 16, V (1115 + 3 * t) =
        Assumptions.bf16Pair (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t)))
          (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t + 1)))) ∧
      Rd (V 2885) (max r0 (max (w0Loc sc w) (w0FE w.pm))) ∧
      Rd (lookupD (f_mst x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3) (w.pw 4)
        (w.pw 5) (w.pw 6) (w.pw 7)) 1109) (w0Loc sc w) := by
  intro V
  exact (w0_block_full hw hx hm hl hmx).1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- The block's reads are the words `w` of a trace block. -/
structure BlkIs (b : Blk) (w : W0Words) : Prop where
  hi : b.hi = w.hi
  mw : b.mw = w.mw
  pw : ∀ j, b.pw j = w.pw j
  pm : b.pm = w.pm
  vt : b.vt = w.vt

/-- The facts at the probability stores of block `b`. -/
def blkOst (x : BitVec 64) (b : Blk) : Nat → Value :=
  lookupD (f_ost x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3) (b.pw 4)
    (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt)

/-- The facts at the row-maximum store of block `b`. -/
def blkMst (x : BitVec 64) (b : Blk) : Nat → Value :=
  lookupD (f_mst x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3) (b.pw 4)
    (b.pw 5) (b.pw 6) (b.pw 7))

/-- **The value of a block.** -/
theorem w0_block {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {x : BitVec 64}
    (hx : Rd (.bits 32 x) (sc : EReal)) {b : Blk} (hb : BlkIs b w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0) :
    Rd (blkOst x b 2950) ((w0Max sc mR w : ℝ) : EReal) ∧
      Rd (blkOst x b 2955) (((w0Next sc (mR, lR) w).2 : ℝ) : EReal) ∧
      (∀ t < 16, blkOst x b (1115 + 3 * t) =
        Assumptions.bf16Pair (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t)))
          (w0Prob sc (w0Max sc mR w) (w0Score w (2 * t + 1)))) ∧
      Rd (blkOst x b 2885) (max r0 (max (w0Loc sc w) (w0FE w.pm))) := by
  have h := w0_block_vars hw hx hm hl hmx (lo := b.lo) (sk := b.sk)
  obtain ⟨h1, h2, h3, h4, -⟩ := show _ ∧ _ ∧ _ ∧ _ ∧ _ from h
  simp only [blkOst, hb.hi, hb.mw, hb.pm, hb.vt, hb.pw]
  exact ⟨h1, h2, h3, h4⟩

/-- **The row maximum a block stores**: the register the store at pc 566 reads (id 1109) reads as
the lane's own scaled maximum `w0Loc`. The facts at the store do not use the peer's word or the
vote, so only the block's loads before the store are named. -/
theorem w0_block_mst {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {x : BitVec 64}
    (hx : Rd (.bits 32 x) (sc : EReal)) {b : Blk} (hhi : b.hi = w.hi) (hmw : b.mw = w.mw)
    (hpw : ∀ j, b.pw j = w.pw j) {mR lR : ℝ} (hm : Rd b.m (mR : EReal))
    (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0) :
    Rd (blkMst x b 1109) (w0Loc sc w) := by
  have h0 := w0_block_vars hw hx hm hl hmx (lo := b.lo) (sk := b.sk)
  obtain ⟨-, -, -, -, h⟩ := show _ ∧ _ ∧ _ ∧ _ ∧ _ from h0
  simp only [blkMst, hhi, hmw, hpw]
  exact h

/-- The register the store at pc 566 reads is a four-byte value of the kind of a row maximum
(`SK.ni`): the clean finite number or the pattern of negative infinity. -/
theorem w0_block_mst_has {sc : ℝ} {w : W0Words} (hw : W0Ok sc w) {x : BitVec 64}
    (hx : Rd (.bits 32 x) (sc : EReal)) {b : Blk} (hhi : b.hi = w.hi) (hmw : b.mw = w.mw)
    (hpw : ∀ j, b.pw j = w.pw j) {mR lR : ℝ} (hm : Rd b.m (mR : EReal))
    (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0) :
    SK.ni.Has (blkMst x b 1109) := by
  obtain ⟨-, -, -, -, -, h⟩ := w0_block_full_has hw hx hm hl hmx (lo := b.lo) (sk := b.sk)
  simp only [blkMst, hhi, hmw, hpw]
  exact h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
