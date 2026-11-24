-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the final chunks 4 to 7 of stage 0

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
/-- The products of final chunk 4 of stage 0. -/
theorem fldW_run_0_4 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4449 (facts L g ⟨.fldW 0 4, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 4, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 4 0 0).pc (facts L g ⟨.fst 0 4 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 4, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 4) rfl hF (base := 3417) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 4, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5133) (base := 3417) (M := 5141)
    (c := 5068) (V := 3433) (o := o) (vc := fcPair ⟨.fldW 0 4, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 4 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 5 of stage 0. -/
theorem fldW_run_0_5 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4484 (facts L g ⟨.fldW 0 5, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 5, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 5 0 0).pc (facts L g ⟨.fst 0 5 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 5, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 5) rfl hF (base := 3457) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 5, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5149) (base := 3457) (M := 5157)
    (c := 5068) (V := 3473) (o := o) (vc := fcPair ⟨.fldW 0 5, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 5 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 6 of stage 0. -/
theorem fldW_run_0_6 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4519 (facts L g ⟨.fldW 0 6, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 6, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 6 0 0).pc (facts L g ⟨.fst 0 6 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 6, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 6) rfl hF (base := 3497) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 6, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5165) (base := 3497) (M := 5173)
    (c := 5068) (V := 3513) (o := o) (vc := fcPair ⟨.fldW 0 6, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 6 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 7 of stage 0. -/
theorem fldW_run_0_7 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4554 (facts L g ⟨.fldW 0 7, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 7, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 7 0 0).pc (facts L g ⟨.fst 0 7 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 7, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 7) rfl hF (base := 3537) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 7, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5181) (base := 3537) (M := 5189)
    (c := 5068) (V := 3553) (o := o) (vc := fcPair ⟨.fldW 0 7, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 7 0 0, i, tt, aw, a, o⟩)
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
