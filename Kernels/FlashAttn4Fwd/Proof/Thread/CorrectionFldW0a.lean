-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionChunk

@[expose] public section

/-! # The products of the final chunks 0 to 3 of stage 0

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
/-- The products of final chunk 0 of stage 0. -/
theorem fldW_run_0_0 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4309 (facts L g ⟨.fldW 0 0, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 0, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 0 0 0).pc (facts L g ⟨.fst 0 0 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 0, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 0) rfl hF (base := 3257) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 0, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5069) (base := 3257) (M := 5077)
    (c := 5068) (V := 3273) (o := o) (vc := fcPair ⟨.fldW 0 0, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 0 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 1 of stage 0. -/
theorem fldW_run_0_1 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4344 (facts L g ⟨.fldW 0 1, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 1, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 1 0 0).pc (facts L g ⟨.fst 0 1 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 1, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 1) rfl hF (base := 3297) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 1, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5085) (base := 3297) (M := 5093)
    (c := 5068) (V := 3313) (o := o) (vc := fcPair ⟨.fldW 0 1, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 1 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 2 of stage 0. -/
theorem fldW_run_0_2 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4379 (facts L g ⟨.fldW 0 2, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 2, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 2 0 0).pc (facts L g ⟨.fst 0 2 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 2, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 2) rfl hF (base := 3337) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 2, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5101) (base := 3337) (M := 5109)
    (c := 5068) (V := 3353) (o := o) (vc := fcPair ⟨.fldW 0 2, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 2 0 0, i, tt, aw, a, o⟩)
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
/-- The products of final chunk 3 of stage 0. -/
theorem fldW_run_0_3 {mem0 : Mem0} {g : Nat} (_hpre : Pre P L mem0) {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {t : TState} (h : At t 4414 (facts L g ⟨.fldW 0 3, i, tt, aw, a, o⟩)) :
    (finOk o (fcPair ⟨.fldW 0 3, i, tt, aw, a, o⟩) = true →
      ∃ t', run kernel asms L g 32 t = some t' ∧
        At t' (Site.fst 0 3 0 0).pc (facts L g ⟨.fst 0 3 0 0, i, tt, aw, a, o⟩)) ∧
    (finOk o (fcPair ⟨.fldW 0 3, i, tt, aw, a, o⟩) = false →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hF := h.2.2.2.2
  have hv := fldW_reg (st := 0) (j := 3) rfl hF (base := 3377) (by decide)
  have hc0 : t.regs 5068 = some (fcPair ⟨.fldW 0 3, i, tt, aw, a, o⟩) :=
    holds_mem hF (mem_factsFrom (by table_decide))
  obtain ⟨hok, hdead⟩ := fchunk_run (L := L) (g := g) (P := 5117) (base := 3377) (M := 5125)
    (c := 5068) (V := 3393) (o := o) (vc := fcPair ⟨.fldW 0 3, i, tt, aw, a, o⟩)
    (w := valueOf L g ⟨.fst 0 3 0 0, i, tt, aw, a, o⟩)
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
