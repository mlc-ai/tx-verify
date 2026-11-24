-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the rescale chunks 0 to 3 of stage 0

From the implicit wait of rescale load `j` (one instruction on, at its first sub-step), the
chunk's packs and multiplications by `α` and its eight unpacks (`rchunk_run`) reach the chunk's
`tcgen05.st` with the products in its source registers, or the thread is dead. The first chunk
also packs `α` twice; it needs the word of `α` to have four bytes. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- The products of rescale chunk 0 of stage 0. -/
theorem rldW_run_0_0 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (hb : aw.bytes = 4) (h : At t 3859 (facts L g ⟨.rldW 0 0, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 25 t = some t' ∧
       At t' (Site.rst 0 0).pc (facts L g ⟨.rst 0 0, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 0) rfl hF (base := 2735) (by decide)
  have ha0 : t.regs 663 = some aw ∧ aw.bytes = 4 :=
    ⟨holds_mem hF (mem_factsFrom (by table_decide)), hb⟩
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4806) (base := 2735) (M := 4815)
    (c := 4814) (U := 2751) (ex := [(4814, 663, 663)]) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 0, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by simp; exact ⟨aw, ha0⟩) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [packRun_val _ _ _ (by decide)
        (List.mem_append_right _ (List.mem_singleton_self _))]
      simp [ha0.1])
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
/-- The products of rescale chunk 1 of stage 0. -/
theorem rldW_run_0_1 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (h : At t 3886 (facts L g ⟨.rldW 0 1, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 0 1).pc (facts L g ⟨.rst 0 1, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 1) rfl hF (base := 2767) (by decide)
  have hc0 : t.regs 4814 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4823) (base := 2767) (M := 4831)
    (c := 4814) (U := 2783) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 1, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 2 of stage 0. -/
theorem rldW_run_0_2 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (h : At t 3912 (facts L g ⟨.rldW 0 2, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 0 2).pc (facts L g ⟨.rst 0 2, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 2) rfl hF (base := 2799) (by decide)
  have hc0 : t.regs 4814 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4839) (base := 2799) (M := 4847)
    (c := 4814) (U := 2815) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 2, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 3 of stage 0. -/
theorem rldW_run_0_3 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (h : At t 3938 (facts L g ⟨.rldW 0 3, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 0 3).pc (facts L g ⟨.rst 0 3, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 0) (j := 3) rfl hF (base := 2831) (by decide)
  have hc0 : t.regs 4814 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4855) (base := 2831) (M := 4863)
    (c := 4814) (U := 2847) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 0 3, i, tt, aw, a, o⟩)
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
