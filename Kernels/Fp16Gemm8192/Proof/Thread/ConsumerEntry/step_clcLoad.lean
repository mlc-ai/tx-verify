-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base

@[expose] public section

/-! One step of `ConsumerEntry`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The response read: a response value reaches the status query. -/
theorem step_clcLoad {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (_hpre : Pre P L mem0) (hs : d.site = .clcLoad) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    (next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_711)
  obtain ⟨a, bs, rfl, rfl⟩ := fires_load rfl rfl hf
  have hr := Flow.response_step (K := kernel) (A := Prod) (L := L) (g := g) (bs := bs)
    (pc := Site.clcLoad.pc) (by decide) Flow.code_712 Flow.code_713 Flow.code_714 h.1 h.2.1
    h.2.2.1 h.2.2.2.1 prod_noUnpack128 prod_noPack128
  cases hq : Flow.responseOf bs with
  | none => exact .inr ⟨by simp [next, hq], hr.2 (Flow.responseOf_none.mp hq)⟩
  | some rr =>
    obtain ⟨t', hl, hpc, hsub, hacc, hf', hd, hframe⟩ := hr.1 rr (Flow.responseOf_some.mp hq)
    refine .inl (.inr ⟨⟨.clcStatus, m, n, m', n', cp, ap, .clc rr, x, acc, base⟩, t',
      by simp [next, hq], hl, ⟨by rw [hpc]; rfl, hsub, hacc, hf', ?_⟩,
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩)
    frame_fp h.2.2.2.2, hframe
    refine ⟨?_, trivial⟩
    rw [hd]
    cons_values

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
