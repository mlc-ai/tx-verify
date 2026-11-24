-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk3Shape
public import Kernels.InklingRelDecode.Proof.Thread.Lk3Min

@[expose] public section

/-!
# The butterfly minimum of `alpha` within a warp (`shfl7` to `shfl10`)

The four exchanges before the scratch store are full-warp `shfl.sync.bfly` with the offsets 8, 4,
2, 1 of `alpha` (`D.stg.al`) and of the running minima `cm1`, `cm2`, `cm3`; each step takes the
minimum of the thread's word and the received one. This file gives their event shapes, their
predecessors and their successors on words that read as numbers.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

theorem shape_shfl7 (hF : Fired L g d e (some u)) (hs : d.site = .shfl7) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.al 8 31 recv ok⟩ := by
  have hpc : d.site.pc = 2242 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_7) hF
  rw [hpc] at hf
  have hr : t.regs 507 = some d.stg.al := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly (p := none) (i := 8) (n := 8) (by decide) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

theorem shape_shfl8 (hF : Fired L g d e (some u)) (hs : d.site = .shfl8) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.cm1 4 31 recv ok⟩ := by
  have hpc : d.site.pc = 2244 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_8) hF
  rw [hpc] at hf
  have hr : t.regs 1536 = some d.stg.cm1 := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly (p := none) (i := 4) (n := 4) (by decide) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

theorem shape_shfl9 (hF : Fired L g d e (some u)) (hs : d.site = .shfl9) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.cm2 2 31 recv ok⟩ := by
  have hpc : d.site.pc = 2246 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_9) hF
  rw [hpc] at hf
  have hr : t.regs 1538 = some d.stg.cm2 := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly (p := none) (i := 2) (n := 2) (by decide) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

theorem shape_shfl10 (hF : Fired L g d e (some u)) (hs : d.site = .shfl10) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.cm3 1 31 recv ok⟩ := by
  have hpc : d.site.pc = 2248 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_10) hF
  rw [hpc] at hf
  have hr : t.regs 1540 = some d.stg.cm3 := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly (p := none) (i := 1) (n := 1) (by decide) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
