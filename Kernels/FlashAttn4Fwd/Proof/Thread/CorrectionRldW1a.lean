-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the rescale chunks 0 to 3 of stage 1

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
/-- The products of rescale chunk 0 of stage 1. -/
theorem rldW_run_1_0 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (hb : aw.bytes = 4) (h : At t 4078 (facts L g ⟨.rldW 1 0, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 25 t = some t' ∧
       At t' (Site.rst 1 0).pc (facts L g ⟨.rst 1 0, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 0) rfl hF (base := 2993) (by decide)
  have ha0 : t.regs 664 = some aw ∧ aw.bytes = 4 :=
    ⟨holds_mem hF (mem_factsFrom (by table_decide)), hb⟩
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4936) (base := 2993) (M := 4945)
    (c := 4944) (U := 3009) (ex := [(4944, 664, 664)]) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 0, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 1 of stage 1. -/
theorem rldW_run_1_1 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (h : At t 4105 (facts L g ⟨.rldW 1 1, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 1 1).pc (facts L g ⟨.rst 1 1, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 1) rfl hF (base := 3025) (by decide)
  have hc0 : t.regs 4944 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4953) (base := 3025) (M := 4961)
    (c := 4944) (U := 3041) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 1, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 2 of stage 1. -/
theorem rldW_run_1_2 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (h : At t 4131 (facts L g ⟨.rldW 1 2, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 1 2).pc (facts L g ⟨.rst 1 2, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 2) rfl hF (base := 3057) (by decide)
  have hc0 : t.regs 4944 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4969) (base := 3057) (M := 4977)
    (c := 4944) (U := 3073) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 2, i, tt, aw, a, o⟩)
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
/-- The products of rescale chunk 3 of stage 1. -/
theorem rldW_run_1_3 (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value} {a : ℝ} {o : List Value}
    {t : TState} (h : At t 4157 (facts L g ⟨.rldW 1 3, i, tt, aw, a, o⟩)) :
    (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g 24 t = some t' ∧
       At t' (Site.rst 1 3).pc (facts L g ⟨.rst 1 3, i, tt, aw, a, o⟩)) ∧
    (chunkOk o (joinValue aw aw) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := rldW_reg (st := 1) (j := 3) rfl hF (base := 3089) (by decide)
  have hc0 : t.regs 4944 = some (joinValue aw aw) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := rchunk_run (L := L) (g := g) (P := 4985) (base := 3089) (M := 4993)
    (c := 4944) (U := 3105) (ex := []) (o := o) (vc := joinValue aw aw)
    (w := valueOf L g ⟨.rst 1 3, i, tt, aw, a, o⟩)
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
