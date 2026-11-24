-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the rescale chunks 4 to 7 of stage 0

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
/-- The products of rescale chunk 4 of stage 0. -/
theorem rldW_run_0_4 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 3964 (facts L g ⟨.rldW 0 4, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 0 4).pc (facts L g ⟨.rst 0 4, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 4) rfl hF (base := 2863) (by decide)
  have hc0 : t.regs 4814 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4871) (base := 2863) (M := 4879)
    (c := 4814) (U := 2879) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 4, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 5 of stage 0. -/
theorem rldW_run_0_5 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 3990 (facts L g ⟨.rldW 0 5, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 0 5).pc (facts L g ⟨.rst 0 5, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 5) rfl hF (base := 2895) (by decide)
  have hc0 : t.regs 4814 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4887) (base := 2895) (M := 4895)
    (c := 4814) (U := 2911) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 5, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 6 of stage 0. -/
theorem rldW_run_0_6 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4016 (facts L g ⟨.rldW 0 6, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 0 6).pc (facts L g ⟨.rst 0 6, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 6) rfl hF (base := 2927) (by decide)
  have hc0 : t.regs 4814 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4903) (base := 2927) (M := 4911)
    (c := 4814) (U := 2943) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 6, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 7 of stage 0. -/
theorem rldW_run_0_7 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4042 (facts L g ⟨.rldW 0 7, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 0 7).pc (facts L g ⟨.rst 0 7, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 7) rfl hF (base := 2959) (by decide)
  have hc0 : t.regs 4814 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4919) (base := 2959) (M := 4927)
    (c := 4814) (U := 2975) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 7, i, tt, aw, a, o⟩)
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
