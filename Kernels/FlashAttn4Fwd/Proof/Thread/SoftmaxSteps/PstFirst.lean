-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The first tile's probability stores

Each `tcgen05.st` of the first tile continues at the next instruction; the segment to the next
site unpacks the next half-precision words (`mov.b64 {a, b}`), or is empty before a
`tcgen05.wait::st`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem step_pst0 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (c : Fin 4)
    (hs : d.site = .pst false c) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  rcases fin4_cases c with rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_0)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 1097 64 h (by table_decide) rfl) (tmem_lt hw8 64
      (by decide)) hf
    refine step_of_run (d' := ⟨.pst false 1, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨8, ?_⟩
    exact (seg_outs (pc := 2530) (liveS := Flow.live 2529 ++ []) (items := pst0a)
      (W := valueOf L g ⟨.pst false 1, i, tt, s, m, l⟩)
      (by decide +kernel) (by decide +kernel) (by kernel_rfl) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by unpacks_ok) (by kernel_rfl)) _ (At.next h)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_1)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 1099 80 h (by table_decide) rfl) (tmem_lt hw8 80
      (by decide)) hf
    refine step_of_run (d' := ⟨.pst false 2, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨8, ?_⟩
    exact (seg_outs (pc := 2539) (liveS := Flow.live 2538 ++ []) (items := pst0b)
      (W := valueOf L g ⟨.pst false 2, i, tt, s, m, l⟩)
      (by decide +kernel) (by decide +kernel) (by kernel_rfl) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by unpacks_ok) (by kernel_rfl)) _ (At.next h)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_2)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 1095 96 h (by table_decide) rfl) (tmem_lt hw8 96
      (by decide)) hf
    refine step_of_run (d' := ⟨.pwait false 0, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_3)
    obtain ⟨-, rfl⟩ := fires_tcSt (reg_tmem 1098 112 h (by table_decide) rfl) (tmem_lt hw8 112
      (by decide)) hf
    refine step_of_run (d' := ⟨.pwait false 1, i, tt, s, m, l⟩) (by simp [next])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨0, ?_⟩
    sm_seg (At.next h) hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
