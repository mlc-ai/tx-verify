-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.SegQ
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepMma

@[expose] public section

/-! # The MMA warp's obligations at the query's load and copy

The eight TMA loads, the arrival and wait on `bar_q_tma`, the sixteen `tcgen05.cp` (which continue
at the next instruction by `fires_tcCp_next`), their commit and wait, and the block loop's entry. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_qLoad (d : D) (hs : ∃ k, d.site = .qLoad k) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  mma_sites s

theorem stepAt_qCopy (d : D) (hs : ∃ k, d.site = .qCopy k) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  mma_sites s except [.qCopy _ => (by mma_issue fires_tcCp_next)]

theorem stepAt_qArrive (d : D) (hs : d.site = .qArrive) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_qWait (d : D) (hs : d.site = .qWait) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_qFence (d : D) (hs : d.site = .qFence) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_qCopyCommit (d : D) (hs : d.site = .qCopyCommit) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_qCopyWait (d : D) (hs : d.site = .qCopyWait) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_qCopyFence (d : D) (hs : d.site = .qCopyFence) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
