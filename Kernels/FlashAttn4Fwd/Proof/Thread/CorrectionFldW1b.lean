-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the final chunks 4 to 7 of stage 1

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
/-- The products of final chunk 4 of stage 1. -/
theorem fldW_run_1_4 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4745 (facts L g ⟨.fldW 1 4, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 4, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 4 0 0).pc (facts L g ⟨.fst 1 4 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 4, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 4) rfl hF (base := 3740) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 4, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5264) (base := 3740) (M := 5272)
    (c := 5199) (V := 3756) (o := o) (vc := fcPair ⟨.fldW 1 4, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 4 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 5 of stage 1. -/
theorem fldW_run_1_5 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4780 (facts L g ⟨.fldW 1 5, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 5, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 5 0 0).pc (facts L g ⟨.fst 1 5 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 5, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 5) rfl hF (base := 3780) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 5, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5280) (base := 3780) (M := 5288)
    (c := 5199) (V := 3796) (o := o) (vc := fcPair ⟨.fldW 1 5, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 5 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 6 of stage 1. -/
theorem fldW_run_1_6 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4815 (facts L g ⟨.fldW 1 6, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 6, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 6 0 0).pc (facts L g ⟨.fst 1 6 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 6, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 6) rfl hF (base := 3820) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 6, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5296) (base := 3820) (M := 5304)
    (c := 5199) (V := 3836) (o := o) (vc := fcPair ⟨.fldW 1 6, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 6 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 7 of stage 1. -/
theorem fldW_run_1_7 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4850 (facts L g ⟨.fldW 1 7, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 1 7, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 1 7 0 0).pc (facts L g ⟨.fst 1 7 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 1 7, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 1) (j := 7) rfl hF (base := 3860) (by decide)
  have hc0 : t.regs 5199 = some (fcPair ⟨.fldW 1 7, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5312) (base := 3860) (M := 5320)
    (c := 5199) (V := 3876) (o := o) (vc := fcPair ⟨.fldW 1 7, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 1 7 0 0, i, tt, aw, a, o⟩)
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
