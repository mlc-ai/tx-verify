-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.Base

@[expose] public section

/-! One step of `LoaderSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- A load that is not the block's last continues to the next load. -/
theorem step_load {P : Params} {L : Launch} {mem0 : Mem0} {g m n q cp x : Nat} {r : Value}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (b : Fin 8) (j : Fin 3)
    (hj : j.val + 1 < 3) (hi : Inv ⟨.load b j, m, n, q, cp, r, x⟩)
    (h : At t (Site.load b j).pc (facts L g ⟨.load b j, m, n, q, cp, r, x⟩))
    (hc : kernel.code[(Site.load b j).pc]? = some ins)
    (hf : Fires (Site.load b j).pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ d' t', next L g ⟨.load b j, m, n, q, cp, r, x⟩ e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d' := by
  have hm : m < 16 := hi.m
  have hn : n < 32 := hi.n
  have hq : q < 128 := hi.q
  obtain ⟨ins', hc', -, hadv, -⟩ := code_advances ⟨.load b j, b, j, .inl rfl⟩
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_next hadv hf
  have h1 := At.next h
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g (betweenLoads b j.val) (PTX.next t) = some t' ∧
      At t' (Site.load b ⟨j.val + 1, hj⟩).pc (facts L g ⟨.load b ⟨j.val + 1, hj⟩, m, n, q, cp, r,
        x⟩) := by
    fin_cases b <;> fin_cases j <;> first | (simp at hj; done) | loader_seg h1 hpre
  refine ⟨⟨.load b ⟨j.val + 1, hj⟩, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
  simp [next, hj]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
