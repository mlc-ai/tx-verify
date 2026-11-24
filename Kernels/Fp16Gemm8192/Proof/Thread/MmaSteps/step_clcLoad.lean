-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! One step of `MmaSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The response read: a response value reaches the status query. -/
theorem step_clcLoad {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} (_hpre : Pre P L mem0) (hs : d.site = .clcLoad) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.mem { kind := .load, space := some (.shared .cta), sem := .acquire,
              scope := some .cta, elem := .int .b 128, addr := ⟨.reg 851 32, 0⟩,
              dsts := [some 974] })) e (some u)) :
    (next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  obtain ⟨a, bs, rfl, rfl⟩ := fires_load rfl rfl hf
  have hr := Flow.response_step (K := kernel) (A := Prod) (L := L) (g := g) (bs := bs)
    (pc := Site.clcLoad.pc) (by decide) Flow.code_499 Flow.code_500 Flow.code_501 h.1 h.2.1
    h.2.2.1 h.2.2.2.1 prod_noUnpack128 prod_noPack128
  cases hq : Flow.responseOf bs with
  | none => exact .inr ⟨by simp [next, hq], hr.2 (Flow.responseOf_none.mp hq)⟩
  | some rr =>
    obtain ⟨t', hl, hpc, hsub, hacc, hf', hd, hframe⟩ := hr.1 rr (Flow.responseOf_some.mp hq)
    refine .inl (.inr ⟨⟨.clcStatus, w, q, fp, ap, cp, .clc rr, x⟩, t', by simp [next, hq], hl,
      ⟨by rw [hpc]; rfl, hsub, hacc, hf', ?_⟩, ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩)
    frame_fp h.2.2.2.2, hframe
    refine ⟨?_, trivial⟩
    rw [hd]
    simp only [valueOf, values, List.cons_append, List.lookup_cons, Nat.reduceBEq,
      Option.getD_some]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
