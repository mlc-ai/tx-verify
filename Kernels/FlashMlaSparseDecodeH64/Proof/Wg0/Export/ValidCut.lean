-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.MustSeen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain

@[expose] public section

/-! # The arrival that closes a block keeps warpgroup 0's trace valid

The closing arrival (pc 1122) follows the fence at pc 1120 (`w0_prev_pc`), which has the vote
behind it (`w0_must`), so the block in progress is voted and its words are valid (`W0Now`); the
new block in progress is empty. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The core of the cut clause**: the closing arrival after a block with a vote keeps a trace
valid. -/
theorem w0Core_cut {sc : ℝ} {l : List Event} {e : Event} (hpc : e.pc = 1122)
    (hvote : ∃ ev ∈ (w0Fin l).2, ev.pc = 578) (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  obtain ⟨ev, hev, hevp⟩ := hvote
  have hok : W0Ok sc (w0Words (w0Fin l).2) := h.now.2 ⟨ev, hev, hevp⟩
  have hfin : w0Fin (l ++ [e]) = ((w0Fin l).1 ++ [(w0Fin l).2], []) := by
    rw [w0Fin_snoc]; simp [hpc, w0ArrSPc]
  have hscan : (w0Scan (l ++ [e])).2 = [] := by
    rw [w0Scan_snoc]; simp [hpc, w0ArrSPc]
  have hn : W0Now sc (l ++ [e]) := by
    refine ⟨?_, ?_⟩
    · rw [hfin]
      intro seg hs
      rcases List.mem_append.mp hs with h1 | h1
      · exact h.now.1 seg h1
      · simp only [List.mem_singleton] at h1; rw [h1]; exact hok
    · rw [hfin]; rintro ⟨a, ha, -⟩; cases ha
  have hea : W0Early sc (l ++ [e]) := by
    unfold W0Early; rw [hfin]; exact Or.inl rfl
  have hsk : w0SkWord (l ++ [e]) = w0SkWord l := w0SkWord_snoc_quiet (by omega)
  have hraw : w0SkRaw (l ++ [e]) = w0SkRaw l := w0SkRaw_snoc_quiet (by omega)
  have hep : W0EpiOk sc (l ++ [e]) := by
    obtain ⟨h1, -, -, h4⟩ := h.epi
    refine ⟨by rw [hsk]; exact h1, Or.inl ?_, Or.inl ?_, by rw [hraw]; exact h4⟩
    · rw [hscan]; simp [w0EpiPe, w0Last]
    · rw [hscan]; simp [w0EpiO, w0Last]
  exact h.snoc hn hea hep

/-- **The closing arrival keeps the trace valid** (the lane's events up to it are no undefined
behaviour). -/
theorem w0Valid_snoc_cut_alive (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat}
    (hal : ∀ j f, X.get (g, j) = some f → j ≤ k → ∀ x, f.kind ≠ .ub x)
    (hw : warp L g < 4) {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 1122)
    (h : W0Valid P.scale ((X.tr g).take k)) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero => exact (Wg0.w0_not_first hp hX hFw he (hal 0 e he (by omega)) (by omega)).elim
    | succ j => exact ⟨j, rfl⟩
  have hb : w0Body e.pc = true := by rw [hpc]; decide
  obtain ⟨f, hf, hfp⟩ := w0_prev_pc hp hX hFw hw he (hal (j + 1) e he le_rfl) hb h
  rw [hpc] at hfp
  have hf1120 : f.pc = 1120 := by simpa [w0Prev] using hfp
  have hfb : w0Body f.pc = true := by rw [hf1120]; decide
  have hm := w0_must hp hX hFw hal hw h j (by omega) f hf hfb (by omega)
  rw [hf1120] at hm
  obtain ⟨ev, hev, hevp⟩ := hm [578] (by decide)
  rw [trace_take_succ he]
  refine w0Core_cut hpc ⟨ev, ?_, by simpa using hevp⟩ h
  rw [w0Fin_snd]; exact hev

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
