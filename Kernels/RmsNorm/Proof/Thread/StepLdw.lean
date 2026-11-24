-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.StepLdx
public import Kernels.RmsNorm.Proof.Thread.SiteTmpl

@[expose] public section

/-! # The weight loads and the reloads of the staged inputs

After the last element of a tile's weight load or its first reload, the thread holds the four
raw values and is at the next load. After the last element of the second reload the code
converts the weights (`widen_chain`), multiplies each reloaded pair by the scale factor and by
its weights (`pack_mul`), converts the products to halves and reaches the output store; a value
the code cannot use stops the machine. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem step_ldwa (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldwa) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldwa.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs =>
      some { d with site := .ldsa0, sub := 0, acc := [], raw := vs }) := fun e => by
    simp only [next, hs]
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  have hpc : t.pc = Site.ldwa.pc := h.1.trans (show d.site.pc = _ by rw [hs])
  have hU : At (afterVec t [167, 170, 173, 176] ([a0, a1, a2] ++ [v])) Site.ldsa0.pc
      (factsAt P g Site.ldsa0.pc { d with site := .ldsa0, sub := 0, acc := [],
                                          raw := [a0, a1, a2] ++ [v] }) := by
    refine ⟨by simp [afterVec, hpc]; rfl, rfl, rfl, by simp [afterVec, setRegs_fault, h.2.2.2.1],
                                                         ?_⟩
    have hframe : ∀ r, r ∉ [167, 170, 173, 176] →
        (setRegs t [167, 170, 173, 176] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [167, 170, 173, 176] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  refine .inl ⟨_, _, by rw [hnext]; rfl, .refl, atD_of rfl rfl hU, ?_⟩
  have := hrow

  inv_tac

theorem step_ldsa0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldsa0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldsa0.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs =>
      some { d with site := .ldsa1, sub := 0, acc := [], rs0 := vs }) := fun e => by
    simp only [next, hs]
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  have hpc : t.pc = Site.ldsa0.pc := h.1.trans (show d.site.pc = _ by rw [hs])
  have hU : At (afterVec t [157, 158, 159, 160] ([a0, a1, a2] ++ [v])) Site.ldsa1.pc
      (factsAt P g Site.ldsa1.pc { d with site := .ldsa1, sub := 0, acc := [],
                                          rs0 := [a0, a1, a2] ++ [v] }) := by
    refine ⟨by simp [afterVec, hpc]; rfl, rfl, rfl, by simp [afterVec, setRegs_fault, h.2.2.2.1],
                                                         ?_⟩
    have hframe : ∀ r, r ∉ [157, 158, 159, 160] →
        (setRegs t [157, 158, 159, 160] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [157, 158, 159, 160] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  refine .inl ⟨_, _, by rw [hnext]; rfl, .refl, atD_of rfl rfl hU, ?_⟩
  have := hrow
  have := hi.raw.1 (.inl hs)
  inv_tac

theorem step_ldwb (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldwb) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldwb.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs =>
      some { d with site := .ldsb0, sub := 0, acc := [], raw := vs }) := fun e => by
    simp only [next, hs]
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  have hpc : t.pc = Site.ldwb.pc := h.1.trans (show d.site.pc = _ by rw [hs])
  have hU : At (afterVec t [225, 228, 231, 234] ([a0, a1, a2] ++ [v])) Site.ldsb0.pc
      (factsAt P g Site.ldsb0.pc { d with site := .ldsb0, sub := 0, acc := [],
                                          raw := [a0, a1, a2] ++ [v] }) := by
    refine ⟨by simp [afterVec, hpc]; rfl, rfl, rfl, by simp [afterVec, setRegs_fault, h.2.2.2.1],
                                                         ?_⟩
    have hframe : ∀ r, r ∉ [225, 228, 231, 234] →
        (setRegs t [225, 228, 231, 234] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [225, 228, 231, 234] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  refine .inl ⟨_, _, by rw [hnext]; rfl, .refl, atD_of rfl rfl hU, ?_⟩
  have := hrow

  inv_tac

theorem step_ldsb0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldsb0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hrow : row g d.i < P.Bt := hi.row (by simp [hs, Site.inRow])
  have hsub4 : d.sub < 4 := hi.sub.1 (by simp [hs, Site.vec])
  have hacc : d.acc.length = d.sub := by simpa [hs, Site.vload] using hi.acc
  have hF : Holds t.regs (factsAt P g Site.ldsb0.pc d) := by rw [← facts_eq hs]; exact h.2.2.2.2
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  have hn : ∀ e, next P g d e = loadNext d e (fun vs =>
      some { d with site := .ldsb1, sub := 0, acc := [], rs0 := vs }) := fun e => by
    simp only [next, hs]
  by_cases hmid : d.sub + 1 < 4
  · exact step_load_mid (by simp [hs, Site.vload]) hn hi h rfl hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨bs, rfl, hdead | ⟨v, hnext, rfl⟩⟩ := load_last hn h rfl h3 hf
  · exact .inr hdead
  obtain ⟨a0, a1, a2, hacc3⟩ := List.length_eq_three.mp (hacc.trans h3)
  rw [hacc3] at hnext ⊢
  have hpc : t.pc = Site.ldsb0.pc := h.1.trans (show d.site.pc = _ by rw [hs])
  have hU : At (afterVec t [215, 216, 217, 218] ([a0, a1, a2] ++ [v])) Site.ldsb1.pc
      (factsAt P g Site.ldsb1.pc { d with site := .ldsb1, sub := 0, acc := [],
                                          rs0 := [a0, a1, a2] ++ [v] }) := by
    refine ⟨by simp [afterVec, hpc]; rfl, rfl, rfl, by simp [afterVec, setRegs_fault, h.2.2.2.1],
                                                         ?_⟩
    have hframe : ∀ r, r ∉ [215, 216, 217, 218] →
        (setRegs t [215, 216, 217, 218] ([a0, a1, a2] ++ [v])).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setRegs, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    change Holds (setRegs t [215, 216, 217, 218] ([a0, a1, a2] ++ [v])).regs _
    frame_fp hF, hframe
    refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> simp [setRegs, setReg] <;> rfl
  refine .inl ⟨_, _, by rw [hnext]; rfl, .refl, atD_of rfl rfl hU, ?_⟩
  have := hrow
  have := hi.raw.1 (.inr hs)
  inv_tac

end
end PTX.Kernels.RmsNorm.Proof
