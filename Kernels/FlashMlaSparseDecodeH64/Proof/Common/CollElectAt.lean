-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElectSt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElectMma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElectTma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElectW0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0

@[expose] public section

/-! # The mask register of a state at an election

`elect_tmpl_at`: a thread state at one of the eight elections (pcs 16, 31, 1350, 1507, 1664, 1822,
1853, 2165) has a template whose static part is the full-mask election. By the one case split on
the thread's state (`state_role`) and the role's facts (`Common/CollElect*.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The program counters of the eight elections. -/
def ElectPc (pc : Nat) : Prop :=
  pc = 16 ∨ pc = 31 ∨ pc = 1350 ∨ pc = 1507 ∨ pc = 1664 ∨ pc = 1822 ∨ pc = 1853 ∨ pc = 2165

/-- **A thread state at an election waits with the full mask.** -/
theorem elect_tmpl_at {σ : (thread P L g).D} (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    {t : TState} {ins : Instr} (hat : (thread P L g).AtD σ t)
    (hc : kernel.code[(thread P L g).pc σ]? = some ins) (he : ElectPc ((thread P L g).pc σ)) :
    Sched.tmplShape (eventTmpl Assumptions.all L g t ins.op) = some (.elect 4294967295) := by
  have h := state_role hJ hi
  generalize (thread P L g).pc σ = q at h hc he
  cases h with
  | startup d n hR hW hx hpc hr =>
    have hcl : d.site.pc ∈ collPcs := by
      rw [← hpc]; unfold ElectPc at he; rcases he with h | h | h | h | h | h | h | h <;>
        simp [h, collPcs]
    rcases startup_coll_site hW hcl with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      rw [hj] at hpc
      fin_cases j <;> simp [Startup.Site.pc] at hpc <;> unfold ElectPc at he <;> omega
    · obtain ⟨site, x1, x2⟩ := d
      simp only at hj
      subst hj
      exact Startup.startup_elect_tmpl j x1 x2 t ins hat hi.1 (by rw [hpc] at hc; exact hc)
  | head s n hs hpc hr hg hw => exfalso; unfold ElectPc at he; omega
  | idle s n hpc hw hr hret => exfalso; unfold ElectPc at he; omega
  | index d n hR hw hpc hr => exfalso; unfold ElectPc at he; omega
  | mma d n hR hok hl hw hpc hr =>
    have hs : d.site = .elect := by
      cases hs : d.site with
      | elect => rfl
      | leave i => exact absurd hs (hl i)
      | qLoad i => simp only [hs, Mma.Site.pc] at hpc; unfold ElectPc at he; omega
      | qCopy i | qk i | pv i =>
        simp only [hs, Mma.Site.pc] at hpc
        split_ifs at hpc <;> unfold ElectPc at he <;> omega
      | _ => simp only [hs, Mma.Site.pc] at hpc; unfold ElectPc at he; omega
    exact Mma.mma_elect_tmpl d hs t ins hat (by rw [hpc] at hc; exact hc)
  | tma d n hR hok hl hw hpc hr =>
    have hs : d.site = .elect := by
      cases hs : d.site with
      | elect => rfl
      | leave i => exact absurd hs (hl i)
      | coord0 i | coord1 i | coord2 i | coord3 i | gather i =>
        have := i.isLt
        simp only [hs, Tma.Site.pc, Tma.coordPc] at hpc
        split_ifs at hpc <;> unfold ElectPc at he <;> omega
      | _ => simp only [hs, Tma.Site.pc] at hpc; unfold ElectPc at he; omega
    exact Tma.tma_elect_tmpl d hs t ins hat (by rw [hpc] at hc; exact hc)
  | dequant d n hR hw hpc hr => exfalso; unfold ElectPc at he; omega
  | wg0 d n hR hw hpc hr =>
    have hcl : (d : Wg0.Control.D).site.pc ∈ collPcs := by
      rw [← hpc]; unfold ElectPc at he; rcases he with h | h | h | h | h | h | h | h <;>
        simp [h, collPcs]
    obtain ⟨c, hs⟩ : ∃ c, (d : Wg0.Control.D).site = .oel c := by
      rw [w0_pc_coll] at hcl
      generalize (d : Wg0.Control.D).site = s at hcl
      cases s <;> simp [Wg0.Site.isOel] at hcl ⊢
    exact Wg0.w0_elect_tmpl d ⟨c, hs⟩ t ins hat hi (by rw [hpc] at hc; exact hc)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
