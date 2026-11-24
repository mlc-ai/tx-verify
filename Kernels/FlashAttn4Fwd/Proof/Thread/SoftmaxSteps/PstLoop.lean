-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The loop tiles' probability stores

Each `tcgen05.st` of a loop tile continues at the next instruction; the segment to the next
site unpacks the next half-precision words (`mov.b64 {a, b}`), or is empty before a
`tcgen05.wait::st`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem step_pst1 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (c : Fin 4)
    (hs : d.site = .pst true c) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  rcases fin4_cases c with rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_4)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 2060 64 h (by table_decide) rfl) (tmem_lt hw8 64
      (by decide)) hf
    refine step_of_run (d' := ⟨.pst true 1, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨8, ?_⟩
    exact (seg_outs (pc := 3545) (liveS := Flow.live 3544 ++ []) (items := pst1a)
      (W := valueOf L g ⟨.pst true 1, i, tt, s, m, l⟩)
      (by decide +kernel) (by decide +kernel) (by kernel_rfl) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by unpacks_ok) (by kernel_rfl)) _ (At.next h)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_5)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 2062 80 h (by table_decide) rfl) (tmem_lt hw8 80
      (by decide)) hf
    refine step_of_run (d' := ⟨.pst true 2, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨8, ?_⟩
    exact (seg_outs (pc := 3554) (liveS := Flow.live 3553 ++ []) (items := pst1b)
      (W := valueOf L g ⟨.pst true 2, i, tt, s, m, l⟩)
      (by decide +kernel) (by decide +kernel) (by kernel_rfl) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by unpacks_ok) (by kernel_rfl)) _ (At.next h)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_6)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 2058 96 h (by table_decide) rfl) (tmem_lt hw8 96
      (by decide)) hf
    refine step_of_run (d' := ⟨.pwait true 0, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_7)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 2061 112 h (by table_decide) rfl) (tmem_lt hw8 112
      (by decide)) hf
    refine step_of_run (d' := ⟨.pwait true 1, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
