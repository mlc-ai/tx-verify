-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SO

@[expose] public section

/-!
# The cells of the softmax region's `tcgen05.st` stores

The kernel has two `tcgen05.st` instructions, both in the softmax region and both of shape
`.16x32bx2`: the store of the probabilities `P` (32 words at `tm + 128 (i % 2)`, half-split 32) and
the store of the rescaled accumulator `O` (64 words at `tm + 256`, half-split 64). Each adds the
thread's warp lane field `warp · 2 ^ 21` to its base column. This file computes the cells of such a
store, the ranges they lie in, and that two threads of the default partition never write a common
cell of one shape: the cell of a half-split store fixes the thread.

* `cell_split`: the cell of register `j` of a `.16x32bx2` store at `ba + w · 2 ^ 21` of thread `g`
  is `⟨cta, 32 (warp % 4) + lane % 16, ba + 32 [lane ≥ 16] + j⟩`-shaped (`off` for the half);
* `pstore_cells`, `ostore_cells`: the cells of the two stores lie in `P b` and in `O` of the
  thread's CTA;
* `split_thread`: two softmax threads of one CTA whose half-split stores (offsets `off`, columns
  `j, j' < off`) share a cell are one thread.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.SO (InS InP InO TmOk)

noncomputable section

/-- **The cell of a half-split `.16x32bx2` access** at the address `ba + w · 2 ^ 21` (`ba` and
the half-split offset below the column field `2 ^ 16`, the lane field a multiple of 32). -/
theorem cell_split (L : Launch) (g ba off w j : Nat) (hba : ba + off < 2 ^ 16) :
    tcDataCell L g (.s16x32bx2 off) (ba + w * 2 ^ 21) j =
      ⟨g / L.block, g % L.block / 32 % 4 * 32 + laneOf L g % 16,
        ba + (if laneOf L g < 16 then 0 else off) + j⟩ := by
  unfold tcDataCell TcShape.base TcShape.columnIn TcShape.laneIn TcShape.lanes chunkOffset laneBase
  by_cases hl : laneOf L g < 16
  · simp only [hl, ↓reduceIte]
    have e1 : (ba + w * 2 ^ 21) / 2 ^ 16 = w * 32 := by omega
    have e2 : (ba + w * 2 ^ 21) % 2 ^ 16 = ba := by omega
    rw [e1, e2]
    have e3 : w * 32 % 32 = 0 := by omega
    have e4 : laneOf L g % 16 = laneOf L g := by omega
    simp only [e3, e4]
    congr 1
  · simp only [hl, ↓reduceIte]
    have e1 : (ba + w * 2 ^ 21 + off) / 2 ^ 16 = w * 32 := by omega
    have e2 : (ba + w * 2 ^ 21 + off) % 2 ^ 16 = ba + off := by omega
    rw [e1, e2]
    have e3 : w * 32 % 32 = 0 := by omega
    simp only [e3]
    congr 1

/-- **The cells of the `P` store of buffer `b`**: register `j < 32` of a thread of CTA `c` is a cell
of `P b` of the CTA. -/
theorem pstore_cells {L : Launch} {g tm b w j c : Nat} (hT : TmOk tm) (hb : b < 2) (hj : j < 32)
    (hc : g / L.block = c) :
    InP tm b (tcDataCell L g (.s16x32bx2 32) (tm + 128 * b + w * 2 ^ 21) j).column ∧
      (tcDataCell L g (.s16x32bx2 32) (tm + 128 * b + w * 2 ^ 21) j).cta = c := by
  have hba : tm + 128 * b + 32 < 2 ^ 16 := by unfold TmOk at hT; omega
  rw [cell_split L g _ 32 w j hba]
  refine ⟨?_, hc⟩
  unfold InP
  simp only
  split_ifs <;> omega

/-- **The cells of the rescale store of `O`**: register `j < 64` of a thread of CTA `c` is a cell
of `O` of the CTA. -/
theorem ostore_cells {L : Launch} {g tm w j c : Nat} (hT : TmOk tm) (hj : j < 64)
    (hc : g / L.block = c) :
    InO tm (tcDataCell L g (.s16x32bx2 64) (tm + 256 + w * 2 ^ 21) j).column ∧
      (tcDataCell L g (.s16x32bx2 64) (tm + 256 + w * 2 ^ 21) j).cta = c := by
  have hba : tm + 256 + 64 < 2 ^ 16 := by unfold TmOk at hT; omega
  rw [cell_split L g _ 64 w j hba]
  refine ⟨?_, hc⟩
  unfold InO
  simp only
  split_ifs <;> omega

/-- **A half-split store's cell fixes the softmax thread.** Two threads `g`, `h` of the default
partition of one CTA (`% block < 128`), with stores at the same base column `ba` and half-split
`off` and registers `j`, `j'` below `off`, that write a common cell are one thread. -/
theorem split_thread {L : Launch} {g h ba off w w' j j' : Nat} (hba : ba + off < 2 ^ 16)
    (hj : j < off) (hj' : j' < off) (hg : g % L.block < 128) (hh : h % L.block < 128)
    (hc : g / L.block = h / L.block)
    (heq : tcDataCell L g (.s16x32bx2 off) (ba + w * 2 ^ 21) j =
      tcDataCell L h (.s16x32bx2 off) (ba + w' * 2 ^ 21) j') : g = h := by
  rw [cell_split L g ba off w j hba, cell_split L h ba off w' j' hba] at heq
  simp only [TcMma.Cell.mk.injEq] at heq
  obtain ⟨h1, h2, h3⟩ := heq
  unfold laneOf at h2 h3
  have : g % L.block = h % L.block := by
    split_ifs at h3 <;> omega
  have hdiv := Nat.div_add_mod g L.block
  have hdiv' := Nat.div_add_mod h L.block
  rw [← hdiv, ← hdiv', hc, this]

end
end PTX.Kernels.InklingRelDecode.Proof.Sr
