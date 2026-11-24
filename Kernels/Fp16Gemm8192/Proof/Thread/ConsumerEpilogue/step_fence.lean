-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Base

@[expose] public section

/-! One step of `ConsumerEpilogue`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem step_fence {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {k : Fin 8}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hw : tidOf L g < 256)
    (hs : d.site = .fence k) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ins', hc', hadv⟩ := epi_fence_code k
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_next hadv hf
  have hm : m < 16 := hi.m
  have hn : n < 32 := hi.n
  have hq : tidOf L g / 32 / 4 < 2 := by omega
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨t2, hr2, ht2⟩ : ∃ t2, run kernel Prod L g (epi_fenceLocals k) (PTX.next t) = some t2 ∧
      At t2 (Site.tma k).pc (facts L g ⟨.tma k, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
    fin_cases k <;> cons_seg (At.next h) hpre
      [epi_r408 m (tidOf L g / 32 / 4) (g / L.block % 2) hm hq hr,
        epi_or_32 n hn, epi_or_64 n hn, epi_or_96 n hn, epi_or_128 n hn, epi_or_160 n hn,
        epi_or_192 n hn, epi_or_224 n hn]
  right
  refine ⟨⟨.tma k, m, n, m', n', cp, ap, resp, x, acc, base⟩, t2, by simp [next],
    run_rtg hr2, ht2, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
