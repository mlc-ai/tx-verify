-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base
public import Lemmas.Flow.Pointer
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.tile_seg

@[expose] public section

/-! One step of `ConsumerEntry`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The group's barrier: the first thread of the group goes to the acknowledgement, the others
to the claimed tile. -/
theorem step_clcBar {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .clcBar)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_720)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (PTX.Op.barSyncN _ _ _) from trivial) hf
  have h1 := At.next h
  have hp8 : (PTX.next t).regs 8 =
      some (.pred (decide ((tidOf L g / 32 % 4 ||| tidOf L g % 32) ≠ 0))) := by
    have hr := reg_val h (show 8 ∈ Flow.live Site.clcBar.pc by table_decide)
    have hv : valueOf L g ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩ 8 =
        .pred (decide ((tidOf L g / 32 % 4 ||| tidOf L g % 32) ≠ 0)) := by
      cons_values
    rw [hv] at hr
    exact hr
  by_cases hfirst : first L g = true
  · -- the group's first thread: the test falls through to the acknowledgement's mapa
    have hd : decide ((tidOf L g / 32 % 4 ||| tidOf L g % 32) ≠ 0) = false := by
      simp only [first, decide_eq_true_eq] at hfirst
      simp [hfirst]
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_721
      (decide ((tidOf L g / 32 % 4 ||| tidOf L g % 32) ≠ 0)) h1 hp8
      (prod_localRule_bra L g _ _ _)
    rw [hd] at ht2
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 3 t2 = some t3 ∧
        At t3 (Flow.bra_721 + 4) (factsAt L g (Flow.bra_721 + 4)
          ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
      cons_seg ht2 hpre
    have hbase := hpre.sharedRange
    unfold sharedBytes at hbase
    have hr101 := reg_val ht3 (show 147 ∈ Flow.live (Flow.bra_721 + 4) by table_decide)
    have hv101 : valueOf L g ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩ 147 =
        b32 (L.sharedBase + 128) := by cons_values
    have hr102 := reg_val ht3 (show 148 ∈ Flow.live (Flow.bra_721 + 4) by table_decide)
    have hv102 : valueOf L g ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩ 148 =
        b32 0 := by cons_values
    rw [hv101] at hr101
    rw [hv102] at hr102
    have hl := readSharedAddress_b32 (L := L) (g := g) (t := t3) (r := 147)
      (x := L.sharedBase + 128) hg (cta_lt hpre hg) (by omega) hr101
    have hrk : readBits L g t3 32 (.reg 148) = .ok 0 := by
      simp [readBits, readReg, hr102, b32, truncBits, bind, Except.bind, pure, Except.pure]
    have hr4 := Flow.run_mapa (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_725 ht3 hl hrk
      (map_zero hpre hg _)
      (hL := prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t3)
    have hr4' : run kernel Prod L g 1 t3 = some (PTX.next (setReg t3 149
        (.ptr 32 false (.shared (g / L.block) (2 *
          ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 128))))) :=
      hr4
    have h2 := At.set (r := 149) (v := .ptr 32 false
        (.shared (g / L.block) (2 * ((g / L.block) / 2)))
        (BitVec.ofNat 64 (L.sharedBase + 128))) ht3
      (Flow.not_mem_factsFrom (live := Flow.live (Flow.bra_721 + 4)) (by table_decide))
    obtain ⟨t5, hr5, ht5⟩ : ∃ t5, run kernel Prod L g 2 (PTX.next (setReg t3 149
        (.ptr 32 false (.shared (g / L.block) (2 *
          ((g / L.block) / 2))) (BitVec.ofNat 64 (L.sharedBase + 128))))) =
        some t5 ∧ At t5 Site.ack.pc (facts L g ⟨.ack, m, n, m', n', cp, ap, resp, x, acc, base⟩) :=
          by
      cons_seg h2 hpre
    have hr := run_comp (run_comp (run_comp hr2 hr3) hr4') hr5
    right
    refine ⟨⟨.ack, m, n, m', n', cp, ap, resp, x, acc, base⟩, t5, ?_, run_rtg hr, ht5,
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩
    simp [next, hfirst]
  · -- the other threads: the test branches to the claimed tile
    have hfalse : first L g = false := by simpa using hfirst
    have hd : decide ((tidOf L g / 32 % 4 ||| tidOf L g % 32) ≠ 0) = true := by
      simp only [first, decide_eq_false_iff_not] at hfalse
      simp [hfalse]
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_721
      (decide ((tidOf L g / 32 % 4 ||| tidOf L g % 32) ≠ 0)) h1 hp8
      (prod_localRule_bra L g _ _ _)
    rw [hd] at ht2
    simp only [↓reduceIte] at ht2
    have hF : Holds t2.regs (factsAt L g (Flow.bra_721 + 8)
        ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩) :=
      Flow.holds_factsFrom_mono (live := Flow.live Site.clcBar.pc) ht2.2.2.2.2 (by table_decide)
    obtain ⟨k, t5, hr5, ht5⟩ := tile_seg hpre hi ⟨ht2.1, ht2.2.1, ht2.2.2.1, ht2.2.2.2.1, hF⟩
    right
    refine ⟨⟨.accWait, m, n, (nextTile ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩).1,
      (nextTile ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩).2, cp, ap, resp, x, acc, base⟩,
      t5, ?_, run_rtg (run_comp hr2 hr5), ht5,
      ⟨hi.1, hi.2, (nextTile_lt hi).1, (nextTile_lt hi).2, hi.5, hi.6, hi.7⟩⟩
    simp [next, hfalse]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
