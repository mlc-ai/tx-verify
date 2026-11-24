-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Base

@[expose] public section

/-! Inclusions of the live registers of consecutive epilogue sites. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

theorem epi_drain_barA_sub (k : Fin 8) :
    ∀ r ∈ Flow.live (Site.barA k).pc, r ∈ Flow.live (Site.drain k).pc := by
  fin_cases k <;> table_decide

theorem epi_barA_store_sub (k : Fin 8) :
    ∀ r ∈ Flow.live (Site.store k 0 0).pc, r ∈ Flow.live (Site.barA k).pc := by
  fin_cases k <;> table_decide

theorem epi_commit_drain_sub (k : Fin 8) (hk : k.val + 1 < 8) :
    ∀ r ∈ Flow.live ((Site.commit k).pc + 1), r ∈ Flow.live (Site.commit k).pc := by
  fin_cases k <;> first | (simp at hk; done) | table_decide

theorem epi_fence_barB_sub (k : Fin 8) :
    ∀ r ∈ Flow.live (Site.fence k).pc, r ∈ Flow.live (Site.barB k).pc := by
  fin_cases k <;> table_decide

theorem epi_exitWait_sub : ∀ r ∈ Flow.live Site.exitWait.pc, r ∈ Flow.live Site.exitArrive.pc := by
  table_decide

theorem epi_exit_wait_sub : ∀ r ∈ Flow.live Site.exit.pc, r ∈ Flow.live Site.exitWait.pc := by
  table_decide

theorem epi_relinquish_sub :
    ∀ r ∈ Flow.live Site.relinquish.pc, r ∈ Flow.live Site.exitWait.pc := by
  table_decide

theorem epi_exit_sub : ∀ r ∈ Flow.live Site.exit.pc, r ∈ Flow.live Site.dealloc.pc := by
  table_decide

theorem epi_finalDrain_sub : ∀ r ∈ Flow.live Site.finalDrain.pc, r ∈ Flow.live Flow.bra_1085 := by
  table_decide

theorem epi_finalDrain_val (L : Launch) (g : Nat) (d d' : D) :
    ∀ r ∈ Flow.live Site.finalDrain.pc, valueOf L g d r = valueOf L g d' r := by
  intro r hr
  have hl : Flow.live Site.finalDrain.pc = [48] := by table_decide
  rw [hl] at hr
  obtain rfl : r = 48 := by simpa using hr
  rfl

theorem epi_store_succ_sub : ∀ (k : Fin 8) (i : Fin 4), i.val + 1 < 4 →
    ∀ r ∈ Flow.live (Flow.store.getD (4 * k.val + (i.val + 1)) 0),
      r ∈ Flow.live (Flow.store.getD (4 * k.val + i.val) 0) := by
  intro k i h
  fin_cases k <;> fin_cases i <;> first | lit_mem | (revert h; decide)

theorem epi_barB_store_sub : ∀ (k : Fin 8) (i : Fin 4), ¬ (i.val + 1 < 4) →
    ∀ r ∈ Flow.live (Flow.bar.getD (2 + 2 * k.val) 0),
      r ∈ Flow.live (Flow.store.getD (4 * k.val + i.val) 0) := by
  intro k i h
  fin_cases k <;> fin_cases i <;> lit_mem

theorem epi_barPred_live (k : Fin 8) : epi_barPred k ∈ Flow.live (Site.barB k).pc := by
  fin_cases k <;> table_decide

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
