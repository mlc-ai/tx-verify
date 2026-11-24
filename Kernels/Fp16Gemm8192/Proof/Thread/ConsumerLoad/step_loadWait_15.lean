-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Base
public import Lemmas.Flow.Pointer
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.CvtTable

@[expose] public section

/-! One step of `ConsumerLoad`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The last load's wait: its conversions, the acknowledgement's `mapa`, then the arrival on the
accumulator barrier. -/
theorem step_loadWait_15 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hw : tidOf L g < 256)
    (hs : d.site = .loadWait 15) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    (next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_900)
  obtain rfl := fires_async_next (show AsyncAdvancesOp PTX.Op.tcWaitLd from trivial) hf
  have hconv := loadWait_conv (L := L) (g := g) (d := ⟨.loadWait 15, m, n, m', n', cp, ap, resp, x,
    acc, base⟩) (cvtTable 15) rfl h
  cases hok : chunkOk acc 15 with
  | false => exact .inr ⟨by simp [next, hok], hconv.2 hok⟩
  | true =>
    obtain ⟨t8, hr8, ht8⟩ := hconv.1 hok
    have hbase := hpre.sharedRange
    unfold sharedBytes at hbase
    obtain ⟨t9, hr9a, ht9⟩ : ∃ t9, run kernel Prod L g 1 t8 = some t9 ∧
        At t9 (Site.accArrive.pc - 3)
          (factsAt L g (Site.accArrive.pc - 3) ⟨.loadWait 15, m, n, m', n', cp, ap, resp, x, acc,
            base⟩) := by
      cons_seg ht8 hpre
    have hr9 : run kernel Prod L g 9 (PTX.next t) = some t9 := run_comp hr8 hr9a
    have hr385 := reg_val_at ht9 (show 431 ∈ Flow.live (Site.accArrive.pc - 3) by table_decide)
    have hv385 : valueOf L g ⟨.loadWait 15, m, n, m', n', cp, ap, resp, x, acc, base⟩ 431 =
        b32 (L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88) := by
      cons_values
    rw [hv385] at hr385
    have hr386 := reg_val_at ht9 (show 432 ∈ Flow.live (Site.accArrive.pc - 3) by table_decide)
    have hv386 : valueOf L g ⟨.loadWait 15, m, n, m', n', cp, ap, resp, x, acc, base⟩ 432 =
        b32 0 := by
      cons_values
    rw [hv386] at hr386
    have hx : L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88 < 2 ^ 32 := by omega
    have hl := readSharedAddress_b32 (L := L) (g := g) (t := t9) (r := 431)
      (x := L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88) hg (cta_lt hpre hg) hx hr385
    have hrk : readBits L g t9 32 (.reg 432) = .ok 0 := by
      simp [readBits, readReg, hr386, b32, truncBits, bind, Except.bind, pure, Except.pure]
    have hr10 := Flow.run_mapa (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_910 ht9 hl
      hrk (map_zero hpre hg _) (prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t9)
    have hr10' : run kernel Prod L g 1 t9 = some (PTX.next (setReg t9 433
        (.ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
            (BitVec.ofNat 64 (L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88))) ) ) := hr10
    have h2 := At.set (r := 433) (v := .ptr 32 false
        (.shared (g / L.block) (2 * ((g / L.block) / 2)))
        (BitVec.ofNat 64 (L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88))) ht9
      (Flow.not_mem_factsFrom (live := Flow.live (Site.accArrive.pc - 3)) (by table_decide))
    obtain ⟨t11, hr11, ht11⟩ : ∃ t11, run kernel Prod L g 2 (PTX.next (setReg t9 433
        (.ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
            (BitVec.ofNat 64 (L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88))) ) ) = some t11 ∧
        At t11 Site.accArrive.pc (facts L g ⟨.accArrive, m, n, m', n', cp, ap, resp, x, acc,
          base⟩) := by
      cons_seg h2 hpre
    refine .inl (.inr ⟨⟨.accArrive, m, n, m', n', cp, ap, resp, x, acc, base⟩, t11, ?_,
      run_rtg (run_comp (run_comp hr9 hr10') hr11), ht11,
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩)
    simp [next, hok]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
