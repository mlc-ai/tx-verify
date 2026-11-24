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

/-- The fence, the `mapa` of the acknowledgement barrier to the leader CTA, and the
zeroing of the trip count; then the acknowledgement's arrival is the next event. -/
theorem step_clcFence {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .clcFence) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t (.fence (.proxy (.async (some (.shared .cta))))))
      e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  have hadv : AdvancesOp (.fence (.proxy (.async (some (.shared .cta))))) := trivial
  obtain rfl := fires_next hadv hf
  have h1 := At.next h
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hcta := cta_lt hpre hg
  -- the two instructions after the fence: the address `%r808` and the zeroed trip count
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 2 (PTX.next t) = some t1 ∧
      At t1 (Site.clcFence.pc + 3) (factsX L g (Site.clcFence.pc + 3)
        ⟨.clcFence, w, q, fp, ap, cp, resp, x⟩
        [(854, b32 (L.sharedBase + 128)), (884, b32 0)]) := by
    mseg h1 hpre
  have hl808 : 854 ∈ Flow.live (Site.clcFence.pc + 3) := by table_decide
  have hl838 : 884 ∈ Flow.live (Site.clcFence.pc + 3) := by table_decide
  have h808 := holds_mem ht1.2.2.2.2 (Flow.mem_factsFrom (val := valueX L g
    ⟨.clcFence, w, q, fp, ap, cp, resp, x⟩ [(854, b32 (L.sharedBase + 128)), (884, b32 0)])
    hl808)
  have h838 := holds_mem ht1.2.2.2.2 (Flow.mem_factsFrom (val := valueX L g
    ⟨.clcFence, w, q, fp, ap, cp, resp, x⟩ [(854, b32 (L.sharedBase + 128)), (884, b32 0)])
    hl838)
  simp only [valueX, List.lookup_cons, Nat.reduceBEq, Option.getD_some] at h808 h838
  have hr2 := Flow.run_mapa (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_509 ht1
    (Flow.readSharedAddress_b32 hg hcta (by omega) h808)
    (show readBits L g t1 32 (.reg 884) = .ok 0 by
      simp [readBits, readReg, h838, b32, truncBits, bind, Except.bind, pure, Except.pure])
    (map_zero hpre hg _)
    (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t1)
  have h2 := At.set (r := 855) (v := ackPtr L g) ht1
    (factsX_ne (show 855 ∉ Flow.live (Site.clcFence.pc + 3) by table_decide))
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 2
      (PTX.next (setReg t1 855 (ackPtr L g))) = some t3 ∧
      At t3 Site.ack.pc (facts L g ⟨.ack, w, 0, fp, ap, cp, resp, x⟩) := by
    mseg h2 hpre
  right
  refine ⟨⟨.ack, w, 0, fp, ap, cp, resp, x⟩, t3, ?_,
    run_rtg (run_comp hr1 (run_comp hr2 hr3)), ht3,
    ⟨hi.w, show 0 < 128 by omega, rfl, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  simp [next]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
