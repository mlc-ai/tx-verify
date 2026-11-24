-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.trip_end

@[expose] public section

/-! One step of `LoaderSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- After block `b`'s arrival the loader goes to the next block, or after the last block
to the end of the trip. -/
theorem step_arrive {P : Params} {L : Launch} {mem0 : Mem0} {g m n q cp x : Nat} {r : Value}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (b : Fin 8)
    (hi : Inv ⟨.arrive b, m, n, q, cp, r, x⟩)
    (h : At t (Site.arrive b).pc (facts L g ⟨.arrive b, m, n, q, cp, r, x⟩))
    (hc : kernel.code[(Site.arrive b).pc]? = some ins)
    (hf : Fires (Site.arrive b).pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ d' t', next L g ⟨.arrive b, m, n, q, cp, r, x⟩ e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d' := by
  have hm : m < 16 := hi.m
  have hn : n < 32 := hi.n
  have hq : q < 128 := hi.q
  obtain ⟨ins', hc', -, hadv, -⟩ := code_advances ⟨.arrive b, b, 0, .inr rfl⟩
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_next hadv hf
  have h1 := At.next h
  by_cases hb : b.val + 1 < 8
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 4 (PTX.next t) = some t' ∧
        At t' (Site.wait ⟨b.val + 1, hb⟩).pc (facts L g ⟨.wait ⟨b.val + 1, hb⟩, m, n, q, cp, r,
          x⟩) := by
      fin_cases b <;> first | (simp at hb; done) | loader_seg h1 hpre
    refine ⟨⟨.wait ⟨b.val + 1, hb⟩, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
    simp [next, hb]
  · have hb7 : b = 7 := Fin.ext (by show b.val = 7; omega)
    subst hb7
    have h1' : At (PTX.next t) ((Site.arrive 7).pc + 1)
        (factsAt L g ((Site.arrive 7).pc + 1) ⟨.arrive 7, m, n, q, cp, r, x⟩) :=
      At.mono h1 (factsAt_mono (pc := (Site.arrive 7).pc) h1.2.2.2.2 (by table_decide))
    obtain ⟨k, t', hr', ht', hi'⟩ := trip_end hpre hi h1'
    refine ⟨endOfTrip ⟨.arrive 7, m, n, q, cp, r, x⟩, t', ?_, run_rtg hr', ht', hi'⟩
    simp [next]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
