-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.LoadBase

@[expose] public section

/-! # The score loads of the first tile

Load `c` (columns `32 c …`, address register `tmem 32 c`) with its implicit wait
(`ld_step`). (After the last load the row maximum follows, `SoftmaxSteps/Max*`.) -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The loads `0`, `1` of the first tile. -/
theorem step_ldFirst01 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (c : Fin 4)
    (hc2 : c.val < 2) (hs : d.site = .ld false c) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
  have hA : At t _ (factsAt L g _ ⟨.ld false c, i, tt, s, m, l⟩) :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by simpa [facts, factsAt, Site.extra] using h.2.2.2.2⟩
  have hframe : ∀ xs,
      Holds t.regs (factsAt L g (Site.ld false c).pc ⟨.ld false c, i, tt, s, m, l⟩) →
      Holds t.regs
        (factsAt L g (Site.ld false c).pc (atWait ⟨.ld false c, i, tt, s, m, l⟩ false c xs)) := by
    intro xs _
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel asms L g 0 t = some t' ∧
        At t' (Site.ld false c).pc
          (factsAt L g (Site.ld false c).pc
            (atWait ⟨.ld false c, i, tt, s, m, l⟩ false c xs)) := by
      rcases fin4_cases c with rfl | rfl | rfl | rfl <;> simp at hc2 <;>
        sm_seg hA hpre
    cases hr'
    exact ht'.2.2.2.2
  rcases fin4_cases c with rfl | rfl | rfl | rfl <;> simp at hc2
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_0)
    have hv : valueOf L g ⟨.ld false 0, i, tt, s, m, l⟩ 1094 = b32 (tmem L g 0) := by
      simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
    refine ld_step rfl hi h
      (tcLdWait_ld false 0)
      (hv ▸ holds_mem hA.2.2.2.2 (List.mem_map.mpr ⟨1094, by table_decide, rfl⟩))
      (by simp only [tmem, stOf, kOf] at hk ⊢; omega) rfl (by decide)
      (show ∀ r ∈ Flow.live Flow.tmemLoad_0, r ∉ ldRegs false 0 by decide +kernel)
      hframe (fun xs _ p hp => ?_) hf
    have hp' : p < 32 := by simpa [ldRegs] using hp
    interval_cases p <;>
      simp only [valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit, Option.getD_some, ldRegs,
        loadW] <;> rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_1)
    have hv : valueOf L g ⟨.ld false 1, i, tt, s, m, l⟩ 1096 = b32 (tmem L g 32) := by
      simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]
    refine ld_step rfl hi h
      (tcLdWait_ld false 1)
      (hv ▸ holds_mem hA.2.2.2.2 (List.mem_map.mpr ⟨1096, by table_decide, rfl⟩))
      (by simp only [tmem, stOf, kOf] at hk ⊢; omega) rfl (by decide)
      (show ∀ r ∈ Flow.live Flow.tmemLoad_1, r ∉ ldRegs false 1 by decide +kernel)
      hframe (fun xs _ p hp => ?_) hf
    have hp' : p < 32 := by simpa [ldRegs] using hp
    interval_cases p <;>
      simp only [valueOf, ctrlValues, floatValues, PTX.Flow.lookupLit, Option.getD_some, ldRegs,
        loadW] <;> rfl
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
