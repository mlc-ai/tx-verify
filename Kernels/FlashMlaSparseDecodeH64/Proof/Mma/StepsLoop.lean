-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.SegQ
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepMma

@[expose] public section

/-! # The MMA warp's obligations in the block loop

Per block: the wait on `bar_dequant_ready`, the sixteen QK and eight PV `.ws` MMAs (which continue
at the next instruction by `fires_tcMma_next`), the two commits, the wait on `bar_so_ready`, the
fences and the loop's end; then the CTA barrier and the `ret`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_qk (d : D) (hs : ∃ k, d.site = .qk k) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  mma_sites s except [.qk _ => (by mma_issue fires_tcMma_next)]

theorem stepAt_pv (d : D) (hs : ∃ k, d.site = .pv k) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  mma_sites s except [.pv _ => (by mma_issue fires_tcMma_next)]

theorem stepAt_kvWait (d : D) (hs : d.site = .kvWait) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_kvFence (d : D) (hs : d.site = .kvFence) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_qkCommit (d : D) (hs : d.site = .qkCommit) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_soWait (d : D) (hs : d.site = .soWait) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_soFence (d : D) (hs : d.site = .soFence) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_pvCommit (d : D) (hs : d.site = .pvCommit) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_outBar (d : D) (hs : d.site = .outBar) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_exit (d : D) (hs : d.site = .exit) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
