-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the rescale chunks 4 to 7 of stage 1

From the implicit wait of rescale load `j` (one instruction on, at its first sub-step), the
chunk's packs and multiplications by `α` and its eight unpacks (`rchunk_run`) reach the chunk's
`tcgen05.st` with the products in its source registers, or the thread is dead. The first chunk
also packs `α` twice; it needs the word of `α` to have four bytes. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch}

set_option maxHeartbeats 8000000 in
/-- The products of rescale chunk 4 of stage 1. -/
theorem rldW_run_1_4 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4183 (facts L g ⟨.rldW 1 4, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 1 4).pc (facts L g ⟨.rst 1 4, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 4) rfl hF (base := 3121) (by decide)
  have hc0 : t.regs 4944 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 5001) (base := 3121) (M := 5009)
    (c := 4944) (U := 3137) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 4, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by simp) (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, rs, rcPair, PTX.Flow.lookupLit])
    (by simp [valueOf, values, chunkValues, loadValues, rcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

set_option maxHeartbeats 8000000 in
/-- The products of rescale chunk 5 of stage 1. -/
theorem rldW_run_1_5 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4209 (facts L g ⟨.rldW 1 5, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 1 5).pc (facts L g ⟨.rst 1 5, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 5) rfl hF (base := 3153) (by decide)
  have hc0 : t.regs 4944 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 5017) (base := 3153) (M := 5025)
    (c := 4944) (U := 3169) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 5, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by simp) (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, rs, rcPair, PTX.Flow.lookupLit])
    (by simp [valueOf, values, chunkValues, loadValues, rcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

set_option maxHeartbeats 8000000 in
/-- The products of rescale chunk 6 of stage 1. -/
theorem rldW_run_1_6 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4235 (facts L g ⟨.rldW 1 6, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 1 6).pc (facts L g ⟨.rst 1 6, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 6) rfl hF (base := 3185) (by decide)
  have hc0 : t.regs 4944 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 5033) (base := 3185) (M := 5041)
    (c := 4944) (U := 3201) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 6, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by simp) (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, rs, rcPair, PTX.Flow.lookupLit])
    (by simp [valueOf, values, chunkValues, loadValues, rcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

set_option maxHeartbeats 8000000 in
/-- The products of rescale chunk 7 of stage 1. -/
theorem rldW_run_1_7 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4261 (facts L g ⟨.rldW 1 7, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 1 7).pc (facts L g ⟨.rst 1 7, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 7) rfl hF (base := 3217) (by decide)
  have hc0 : t.regs 4944 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 5049) (base := 3217) (M := 5057)
    (c := 4944) (U := 3233) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 7, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by simp) (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, rs, rcPair, PTX.Flow.lookupLit])
    (by simp [valueOf, values, chunkValues, loadValues, rcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
