-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Span
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Lemmas.Flow.Step.TcSteps

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow

private def dst (st : Fin 2) (c : Fin 8) : Site :=
  if c.val = 7 then .rwait st else .rld st (c+1)

private theorem store_row (st : Fin 2) (c : Fin 8) :
    ∃ ta ss, kernel.code[(Site.rst st c).pc]? = some ⟨none, .tcSt ta ss .s32x32b⟩ ∧
      Assumptions.all.any (·.tcStWaitLd (Site.rst st c).pc) = false ∧
      (Site.rst st c).pc + 1 = (dst st c).pc ∧
      (liveAt (dst st c)).all (liveAt (.rst st c)).contains = true := by
  have table : ∀ st c, 8000 ≤ (Site.rst st c).pc ∧
      (match tailCode[(Site.rst st c).pc - 8000]? with
       | some ⟨none, .tcSt _ _ .s32x32b⟩ => true | _ => false) = true ∧
      Assumptions.delayedTmemSites.contains (Site.rst st c).pc = false ∧
      (Site.rst st c).pc + 1 = (dst st c).pc ∧
      (liveAt (dst st c)).all (liveAt (.rst st c)).contains = true := by decide +kernel
  obtain ⟨hb, hc, hw, h⟩ := table st c
  rw [← tailCode_eq, List.getElem?_drop, Nat.add_sub_of_le hb] at hc
  split at hc
  · exact ⟨_, _, ‹_›, (Assumptions.all_tcStWaitLd _).trans hw, h⟩
  · cases hc

theorem store_code (st : Fin 2) (c : Fin 8) :
    ∃ ta ss, kernel.code[(Site.rst st c).pc]? = some ⟨none, .tcSt ta ss .s32x32b⟩ ∧
      Assumptions.all.any (·.tcStWaitLd (Site.rst st c).pc) = false := by
  obtain ⟨ta, ss, hc, hw, _⟩ := store_row st c
  exact ⟨ta, ss, hc, hw⟩

theorem stepAt_rstU {p L g} (st : Fin 2) (c : Fin 8) (v : V) :
    (code p L g).StepAtU ⟨.rst st c, v, 0⟩ := by
  obtain ⟨ta, ss, hc, hw, hpc, hsub⟩ := store_row st c
  refine ⟨fun _ => ⟨_, hc, rfl, trivial⟩, ?_⟩
  intro t e u ins hat _ hins hf
  obtain ⟨hpcAt, hsubAt, haccAt, hfaultAt, hregsAt⟩ := hat
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain rfl := fires_tcSt_next (hpcAt ▸ hw) hf
  have hregs := holds_factsFrom_mono hregsAt (fun r hp =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hsub r hp))
  refine .inl (.inr ⟨⟨dst st c, v, 0⟩, PTX.next t, ?_, .refl, .inl ⟨?_, .inl rfl⟩⟩)
  · by_cases h : c.val = 7 <;> simp only [succ, Correction.succ, D.scheduler, dst, h,
      ↓reduceIte, Option.map_some, erase, V.scheduler, Correction.D.mk']
  · refine ⟨(congrArg (·+1) hpcAt).trans hpc, hsubAt, haccAt, hfaultAt, ?_⟩
    unfold dst at hregs ⊢
    split at hregs <;> rename_i h <;> simp only [h, ↓reduceIte] <;> exact hregs

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
