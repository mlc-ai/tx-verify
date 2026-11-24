-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the final chunks 0 to 3 of stage 1

From the implicit wait of final load `j` (one instruction on, at its first sub-step), the
chunk's packs and multiplications by the reciprocal of `l`, its eight unpacks and conversions to
halves (`fchunk_run`), reach the chunk's first `st.shared.v4` with the half-precision words in
its source registers, or the thread is dead. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch}

set_option maxHeartbeats 8000000 in
/-- The products of final chunk 0 of stage 1. -/
theorem fldW_run_1_0 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4605 (facts L g ⟨.fldW 1 0, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 0, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 0 0 0).pc (facts L g ⟨.fst 1 0 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 0, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 0) rfl hF (base := 3580) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 0, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5200) (base := 3580) (M := 5208)
    (c := 5199) (V := 3596) (o := o) (vc := fcPair ⟨.fldW 1 0, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 0 0 0, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCvtCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, fw, fcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

set_option maxHeartbeats 8000000 in
/-- The products of final chunk 1 of stage 1. -/
theorem fldW_run_1_1 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4640 (facts L g ⟨.fldW 1 1, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 1, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 1 0 0).pc (facts L g ⟨.fst 1 1 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 1, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 1) rfl hF (base := 3620) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 1, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5216) (base := 3620) (M := 5224)
    (c := 5199) (V := 3636) (o := o) (vc := fcPair ⟨.fldW 1 1, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 1 0 0, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCvtCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, fw, fcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

set_option maxHeartbeats 8000000 in
/-- The products of final chunk 2 of stage 1. -/
theorem fldW_run_1_2 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4675 (facts L g ⟨.fldW 1 2, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 2, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 2 0 0).pc (facts L g ⟨.fst 1 2 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 2, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 2) rfl hF (base := 3660) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 2, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5232) (base := 3660) (M := 5240)
    (c := 5199) (V := 3676) (o := o) (vc := fcPair ⟨.fldW 1 2, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 2 0 0, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCvtCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, fw, fcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

set_option maxHeartbeats 8000000 in
/-- The products of final chunk 3 of stage 1. -/
theorem fldW_run_1_3 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4710 (facts L g ⟨.fldW 1 3, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 3, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 3 0 0).pc (facts L g ⟨.fst 1 3 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 3, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 3) rfl hF (base := 3700) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 3, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5248) (base := 3700) (M := 5256)
    (c := 5199) (V := 3716) (o := o) (vc := fcPair ⟨.fldW 1 3, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 3 0 0, i, tt, aw, a, o⟩)
    (PackCode.of_bool (by rw [h.1]; decide +kernel))
    (MulCodeE.of_bool (by rw [h.1]; decide +kernel))
    (UnpackCvtCode.of_bool (by rw [h.1]; decide +kernel)) h.2.2.2.1 (by rw [h.1]; decide) hv
    (by decide) (by decide) (by decide) (by decide)
    (by rw [packRun_other _ _ _ (by decide)]; exact hc0)
    (by decide) (by decide) (by decide) (by decide)
    (by intro k hk; interval_cases k <;>
      simp [valueOf, chunkValues, fw, fcPair, PTX.Flow.lookupLit])
  refine ⟨fun hok' => ?_, hdead⟩
  obtain ⟨t', hr, hpc', hsub', hacc', hf', hW, hframe⟩ := hok hok'
  refine ⟨t', hr, by rw [hpc', h.1]; rfl, hsub'.trans h.2.1, hacc'.trans h.2.2.1, hf', ?_⟩
  frame_fp hF, hframe
  exact holds_sub hW (by lit_mem)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
